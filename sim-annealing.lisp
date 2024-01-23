;;;  SOLVE-SA
;;; -------------------------------------
;;;  INPUT:  G, a sudoku game in which all initial forced moves have 
;;;              already been made
;;;  OUTPUT:  A solved puzzle (or NIL)

(defun solve-sa (g))


;; difference from hill-climbing is that it picks a random move instead of thebest  move
;; if the move improves the situation it is always accepted
;; otherwise the algorithm accepts the move with some probability less than 1
;; probablity decreases exponentially based on how poor the move is
;; and how far into the search we are (T)

;; g is game
;; schedule is map from time to "temperature"
(defun solve-sa (g schedule)
    (let ((curr-state (copy-game g))
          (i 1))
        (loop
            (let ((j (schedule i)))
                (if (eq j 0)
                    (return curr-state))
            ;; do-random-move! performs a random legal move on board g
                (let* ((next-state (do-random-move! g))
                ;; value-difference calculate the value based on constraints
                       (vd (value-difference curr-state next-state)))
                    (if (eq vd 0)
                        (setf curr-state next-state))
                    (if (not (eq vd 0))
                ;; prob move does the move with a probability of vd/j
                        (prob-move curr-state next-state vd j))
                )
            )
        )
    )
)

;; From textbook:

;; function solve-sa(problem schedule) returns a solution state
;; (schedule is a mapping from time to "temperature")

;; current <- make-node(problem.initial-state)

;; for t = 1 to inf do

;;      T <- schedule(t)

;;      if T = 0 then return current

;;      next <- a randomly selected successor of current

;;      E <- next.value - current.value

;;      if E = 0 then current <- next
;;      else current <- next only with probability E/T

