(ns stateful-check.command-runner
  (:require [clojure.walk :as walk]
            [stateful-check
             [command-utils :as u]
             [symbolic-values :refer [get-real-value SymbolicValue ->RootVar]]]))

(defmulti step-command-runner
  "Step the command runner state machine one step. Each state in the
  state machine is represented by a \"variant\", which is a vector
  with a key (the state name) and a series of values. What work needs
  to be done in each state is taken care of by this method's
  implementations, and they return a new state variant."
  (fn [spec state state-name & args] state-name))

;; :next-command, :run-command, :next-state, :postcondition-check
;; :done, :fail

(defmethod step-command-runner :next-command
  [spec state _ command-list results]
  [state (if (seq command-list)
           (try (let [[sym-var [command & raw-args]] (first command-list)
                      args (walk/prewalk (fn [value]
                                           (if (satisfies? SymbolicValue value)
                                             (get-real-value value results)
                                             value))
                                         raw-args)]
                  [:run-command
                   [sym-var [command args raw-args]]
                   (next command-list)
                   results])
                (catch Throwable ex
                  [:fail ex]))
           [:done])])

(defmethod step-command-runner :run-command
  [_ state _ [sym-var [command args raw-args] :as current] command-list results]
  [state (try (let [result (u/run-command command args)
                    results (assoc results sym-var result)]
                [:next-state current command-list results result])
              (catch Throwable ex
                (println ex)
                [:fail ex]))])

(defmethod step-command-runner :next-state
  [_ state _ [sym-var [command args raw-args] :as current] command-list results result]
  (try [(u/real-make-next-state command state args result)
        [:postcondition-check
         current
         command-list
         results
         result
         (pr-str result)
         ;; this is for debug purposes, as it effectively
         ;; takes a snapshot of the object at this point
         ]]
       (catch Throwable ex
         [state [:fail ex]])))

(defmethod step-command-runner :postcondition-check
  [_ state _ [sym-var [command args raw-args] :as current] command-list results result _]
  [state [:next-command command-list results]]
  ;; (try (if (u/check-postcondition command prev-state next-state args result)
  ;;        [:next-command spec
  ;;         command-list
  ;;         results
  ;;         next-state]
  ;;        [:fail spec next-state])
  ;;      (catch Throwable ex
  ;;        [:fail spec next-state ex]))
  )

;; terminal state, so return `nil`
(defmethod step-command-runner :fail
  ([spec state _]
   (step-command-runner spec state :fail nil))
  ([spec state _ _]
   (u/run-spec-cleanup spec state)
   nil))
(defmethod step-command-runner :done [spec state _]
  (u/run-spec-cleanup spec state)
  nil)

(defn run-commands
  "Run the given list of commands with the provided initial
  results/state. Returns a lazy seq of states from the command
  runner."
  [spec [state results] command-list]
  (try
    (->> [state [:next-command command-list results]]
         (iterate (fn [[state args]]
                    (apply step-command-runner spec state args)))
         (take-while (complement nil?))
         (map second)
         doall)
    (catch Exception ex
      (println ex))))

(defn passed?
  "Determine whether a list of command runner states represents a
  successfully completed execution."
  [spec [state results] command-results]
  (reduce (fn [[state prev-state] [step & args]]
            (case step
              :next-state
              (let [[[sym-var [command args raw-args] :as current] command-list results result] args]
                [(u/real-make-next-state command state args result) state])

              :postcondition-check
              (let [[[_ [command args _] :as cmd] _ _ result str-result] args]
                (if (u/check-postcondition command prev-state state args result)
                  [state]
                  (reduced false)))

              (:done :fail)
              (= step :done)

              [state prev-state]))
          [state]
          command-results))

(defn extract-exception
  "Return the exception thrown during the execution of commands for
  this result list."
  [command-results]
  (let [[type exception] (last command-results)]
    (if (= type :fail)
      exception)))
