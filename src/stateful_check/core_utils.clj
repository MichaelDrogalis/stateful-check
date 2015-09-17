(ns stateful-check.core-utils
  (:require [clojure.test.check :refer [quick-check]]
            [clojure.test.check
             [generators :as gen]
             [properties :refer [for-all]]
             [rose-tree :as rose]]
            [stateful-check
             [command-runner :as r]
             [command-utils :as u]
             [command-verifier :as v]
             [generator-utils :refer [gen-do]]
             [symbolic-values :refer [->RootVar]]]))

(defmacro assert-val
  ([val]
   (when *assert*
     `(let [val# ~val]
        (if (some? val#)
          val#
          (throw (AssertionError. (str "Assert failed: " (pr-str '~val))))))))
  ([val message]
   (when *assert*
     `(let [val# ~val]
        (if (some? val#)
          val#
          (throw (AssertionError. (str "Assert failed: " ~message))))))))

(defn generate-command-object
  "Generate the object for a command. This means first generating a
  command name using the spec's :model/generate-command function, then
  returning the full command object matching the generated command
  name. The generated name is `assoc`ed onto the command map under
  the :name key."
  [spec state]
  (gen/gen-fmap (fn [rose-tree]
                  (let [command-key (rose/root rose-tree)
                        value (get (:commands spec) command-key)
                        value (if (var? value) @value value)]
                    (assoc (assert-val value (str "Command " command-key " not found in :commands map"))
                           :name command-key)))
                (u/generate-command-name spec state)))

;; Don't remove the `size` parameter to this function! It's there so
;; we can keep track of how "long" the command list is meant to be
;; without also influencing the "size" of the generated commands. You
;; can't use gen/sized because that would also influence the size of
;; the command generators themselves.
(defn generate-commands*
  "Returns a list of rose-trees within the monad of gen/gen-pure. "
  ([spec state size] (generate-commands* spec state size 0))
  ([spec state size count]
   (gen/frequency
    [[1 (gen/gen-pure nil)]
     [size (gen-do command <- (generate-command-object spec state)
                   (if (u/check-requires command state)
                     (gen-do args-rose <- (u/generate-args command state)
                             :let [args (rose/root args-rose)]
                             (if (u/check-precondition command state args)
                               (gen-do :let [result (->RootVar count)
                                             next-state (u/model-make-next-state command state args result)]
                                       roses <- (generate-commands* spec next-state (dec size) (inc count))
                                       (gen/gen-pure (cons (rose/fmap (fn [args]
                                                                        [result (cons command args)])
                                                                      args-rose)
                                                           roses)))
                               (generate-commands* spec state size count)))
                     (generate-commands* spec state size count)))]])))

(defn shrink-roses
  "Shrink the command rose trees (by removing commands and shrinking
  command arguments)."
  [roses]
  (let [singles (rose/remove roses)
        pairs (mapcat (comp rose/remove vec) singles)]
    (concat singles pairs)))

(defn concat-command-roses
  "Take a seq of rose trees and concatenate them. Create a vector from
  the roots along with a rose tree consisting of shrinking each
  element in turn."
  [roses]
  (if (seq roses)
    [(apply vector (map rose/root roses))
     (map concat-command-roses (shrink-roses (vec roses)))]
    [[] []]))

(defn generate-commands
  "Generate a seq of commands from a spec and an initial state."
  [spec state]
  (gen/gen-bind (gen/sized #(generate-commands* spec state %))
                (fn [roses]
                  (gen/gen-pure (concat-command-roses roses)))))

(defn valid-commands?
  "Verify whether a given list of commands is valid (preconditions all
  return true, symbolic vars are all valid, etc.)."
  [spec command-list]
  (let [[state results] (u/model-make-initial-state-and-results spec)]
    (v/valid? command-list results state)))

(defn generate-valid-commands
  "Generate a set of valid commands from a specification"
  [spec]
  (->> (u/model-make-initial-state-and-results spec)
       first ;; we only want the state part
       (generate-commands spec)
       (gen/such-that (partial valid-commands? spec))))

(defn make-failure-exception
  "Make an exception which indicates the failure of a generated test
  case. This is necessary to pass more information up to the function
  which prints the command lists."
  [initial results]
  (ex-info "Generative test failed. See :results for more information."
           {:initial initial,:results results}))

(defn spec->property
  "Turn a specification into a testable property."
  ([spec] (spec->property spec {:tries 1}))
  ([spec {:keys [tries]}]
   (for-all [commands (generate-valid-commands spec)]
     (loop [tries (or tries 1)]
       (if (pos? tries)
         (let [initial (u/real-make-initial-state-and-results spec)
               results (r/run-commands spec initial commands)]
           (if (r/passed? spec initial results)
             (recur (dec tries))
             (throw (make-failure-exception initial results))))
         true)))))

(defn format-command
  "Turn a command entry into a representative string"
  [[sym-var [{name :name} _ args] :as cmd]]
  (str (pr-str sym-var) " = " (pr-str (cons name args))))

(defn print-command-results
  "Print out the results of a `r/run-commands` call. No commands are
  actually run, as the argument to this function contains the results
  for each individual command."
  ([{:keys [results initial]}] (print-command-results results false))
  ([{:keys [results initial]} stacktraces?]
   (try
     (reduce (fn [[state prev-state] [step & args]]
               (case step
                 :next-state
                 (let [[[sym-var [command args raw-args] :as current] command-list results result] args]
                   [(u/real-make-next-state command state args result) state])

                 :postcondition-check
                 (let [[[_ [command args _] :as cmd] _ _ result str-result] args]
                   (println "  " (format-command cmd) "\t=>" str-result)
                   (if (u/check-postcondition command prev-state state args result)
                     [state]
                     (reduced (println "!! postcondition failed !!"))))

                 :fail
                 (let [[exception] args]
                   (println "!! exception thrown:" exception "!!"))

                 [state prev-state]))
             [(first initial)] results)
     (catch Throwable ex
       (println "Unexpected exception thrown in test runner -" ex)
       (.printStackTrace ex (java.io.PrintWriter. ^java.io.Writer *out*))))))

(defn print-test-results
  "Print the results of a test.check test in a more helpful form (each
  command with its corresponding output).

  This function will re-run both the failing test case and the shrunk
  failing test. This means that the commands will be run against the
  live system."
  [spec results {:keys [first-case? stacktraces?]}]
  (when-not (true? (:result results))
    (when first-case?
      (println "First failing test case:")
      (print-command-results (-> results :result ex-data) stacktraces?)
      (println "Shrunk:"))
    (print-command-results (-> results :shrunk :result ex-data) stacktraces?)
    (println "Seed: " (:seed results))
    (println "Visited: " (-> results :shrunk :total-nodes-visited))))

(defn run-specification
  "Run a specification. This will convert the spec into a property and
  run it using clojure.test.check/quick-check. This function then
  returns the full quick-check result."
  ([specification] (run-specification specification nil))
  ([specification {:keys [num-tests max-size seed tries]}]
   (quick-check (or num-tests 100)
                (spec->property specification {:tries tries})
                :seed seed
                :max-size (or max-size 200))))
