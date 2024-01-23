;;;  SOLVE-BT
;;; -------------------------------------
;;;  INPUT:  G, a sudoku game in which all initial forced moves have 
;;;              already been made
;;;  OUTPUT:  A solved puzzle (or NIL)

(defun solve-bt (g)
    ;; call recursive backtracking
    return rec-solve-bt({}, g)
)

(defun rec-solve-bt (assignment g)) ;; returns solution/failure
    ;; if assignment is complete return it
    
    ;; var <- select-unassigned-variable (variables[csp], assignment, g)
    
    ;; for each value in domain-values(var, assignment, g)

    ;;      if value is consistent with assignment given sudoku constraints

    ;;          add {var = value} to assignment

    ;;          result <- recursive-backtracking(assignment g)

    ;;          if result is not a failure
    ;;              return result

    ;;          remove {var = value} from assignment

    ;; return failure