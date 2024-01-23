;;;  SOLVE-HC
;;; -------------------------------------
;;;  INPUT:  G, a sudoku game in which all initial forced moves have 
;;;              already been made
;;;  OUTPUT:  A solved puzzle (or NIL)

(defun solve-hc (g)
    ;; obj-f should be the number of contraints being broken in g
    (let ((obj-f (objective-function g)))
        ;; if no constraints being broken then we solved the puzzle
        (if (eq obj-f 0)
            (return-from solve-hc g))
        ;; get all possible legal moves
        (let ((lm (legal-moves g)))
            ;; loop through list of possible moves
            (dolist (mv lm)
                ;; do the move and put assign it as a new game
                ;; get the obj-func value based on the new-game
                (let* ((new-g (do-move! mv g))
                       (new-obj-f (objective-function new-g)))
                    (cond
                    ;; if new-game has no constraints broken
                        ((eq new-obj-f 0)
                        ;; puzzle solved return the game
                        (return-from solve-hc new-g))
                        ;; if there are less constraints broken in new-game
                        ((< new-obj-f obj-f)
                        ;; we want to continue this way so we call solve-hc
                        ;; on the new-game
                        (let ((rec (solve-hc new-g)))
                            ;; if the game gets solved we return it
                            (if (not (eq rec nil))
                                   (return-from solve-hc rec))))
                        ;; else we continue the loop until solution
                        (t 
                         (setf new-obj-f nil)))))
        ;; went through the list of possible moves and no solutions
        (return-from solve-hc nil))))




;; Evaluate initial game-state

;; If goal achieved then return

;; Else initial state = current state

;; loop for all possible operations to current state

;;      Select a state that has not been applied to current state
;;      Apply it to produce new state

;;      cond:
;;          if current state = goal state return

;;          if new state better then current state
;;              current state = new state 
;;              proceed further

;;          else continue loop until solution found

;;  return failure


;; Objective Function
;; --> an evaluation function for the sudoku grid
;; --> the grid will begin arbitrarily filled in
;; --> function will evaluate the number of contraints failed
;; --> one that checks errors in rows, another for cols, another for boxes
;; --> The goal will be to get the number of errors to zero

;; --> the most effective way will likely be to try and reduce the
;;     constraint with the most errors

;; when we hit local minimum we should reset.


;; From Textbook:

;; function hill-climbing(problem) returns a state that is a local maximum
;;      current <- make-node(problem.initial-state)
;;      loop do
;;          neighbor <- a highest-valued succesor of current
;;          if neighbor.value <= current.value then return current.state
;;          else current <- neighbor