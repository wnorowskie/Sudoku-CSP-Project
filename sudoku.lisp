;;; -----------------------------------------------
;;;  CMPU-365, Fall 2010
;;;  Asmt. 4 Solution -- Sudoku Solver
;;; -----------------------------------------------
;;;  This file contains an implementation of a sudoku solver 
;;;  using constraint satisfaction techniques.  It is non-destructive
;;;  in the sense that it creates new child nodes without modifying their
;;;  parent nodes.  However, it does destructively reduce the domains of 
;;;  the child nodes after it creates them -- but that's okay because 
;;;  the domain reductions never need to be undone:  if the child
;;;  node fails, then we backtrack to its parent.

;;;  The code uses two vectors of length 81 to hold the 81 slots in a
;;;  sudoku puzzle and their corresponding domains.  Although this
;;;  requires a small amount of ugly code (e.g., in the initialization
;;;  of the *CS* array, discussed below), it makes the code faster.
;;;  The domain for each slot is a list of at most 9 numbers.

;;;  A sudoku puzzle has 27 constraints (9 row constraints, 9 column
;;;  constraints and 9 box constraints).  To facilitate dealing with
;;;  these constraints in a uniform manner, each of the 27 constraints
;;;  is represented by specifying the 9 slots (i.e., the 9 indices) it
;;;  governs.  Thus, the collection of 27 constraints is represented
;;;  by a 27x9 array of indices.

;;;  *CS*  --  The 27-by-9 array of constraints

(defparameter *cs* (make-array '(27 9)))

;;;  INITIALIZE THE *CS* ARRAY 
;;; -------------------------------------------------------------------
;;;  Since there is only one *CS* array, and it is fixed for all time,
;;;  we don't even bother to use a function; we just initialize the
;;;  *CS* array automatically when this file is loaded.  The
;;;  initialization expressions are fairly ugly because the values
;;;  stored in the *CS* array are indices into the SLOTS vector (of
;;;  length 81), not *pairs* of indices into a 9-by-9 array.

(dotimes (r 9)
  (dotimes (c 9)
    ;; The ROW constraints are in rows 0 - 8 of the *CS* array
    ;;   (Note that R goes from 0 to 8 in this DOTIMES)
    (setf (aref *cs* r c) 
      (+ (* 9 r) c))
    ;; The COLUMN constraints are in rows 9 - 17 of the *CS* array
    ;;   (Note that (+ R 9) goes from 9 to 17 in this DOTIMES)
    (setf (aref *cs* (+ r 9) c)
      (+ (* 9 c) r))
    ;; The BOX constraints are in rows 18 - 26 of the *CS* array
    ;;   (Note that (+ R 18) goes from 18 to 26 in this do times)
    (setf (aref *cs* (+ r 18) c)
      (+ (* 9 (+ (* 3 (floor (/ r 3))) (floor (/ c 3))))
	 (+ (mod c 3) (* 3 (mod r 3)))))
    ))

;;;  For debugging:  print out the *CS* array
;;; ------------------------------------------------------
;;; (dotimes (r 27) 
;;;   (dotimes (c 9)
;;;     (format t "~A " (aref *cs* r c)))
;;;   (format t "~%"))


;;;  GET-CONSTRAINT-INDICES
;;; -------------------------------------------
;;;  INPUT:  INDY, an index from 0 to 80
;;;  OUTPUT:  A list of the three constraints that INDY is
;;;           governed by (i.e., the three ROWS of the *CS* array
;;;           that represent constraints governing INDY).
;;;  IMPLEMENTATION NOTE:  Because the *CS* array is fixed for 
;;;    all time, the 3-element lists returned by GET-CONSTRAINT-INDICES
;;;    can simply be *stored* in a vector of length 81.  Once this
;;;    vector is initialized, GET-CONSTRAINT-INDICES can just
;;;    do "table lookup" to return the appropriate 3-element list.

;;;  *CONSTRAINT-INDICES*  
;;; --------------------------------------------
;;;  A vector of length 81.  The Ith entry is a 3-element list
;;;  containing the constraints that govern the Ith slot.  

(defparameter *constraint-indices*
    ;; The following expression creates and initializes the
    ;; 81-element vector.
    (let ((veck (make-array 81)))
      (dotimes (indy 81)
	;; First, determine which row and column the slot with
	;; index INDY belongs to in the sudoku puzzle
	(let ((myrow (floor (/ indy 9)))
	      (mycol (mod indy 9)))
	  ;; The row constraint for row, MYROW, corresponds to the
	  ;;   MYROW row of the *CS* array.
	  ;; The column constraint for column, MYCOL, corresponds to
	  ;;   the 9+MYCOL row of the *CS* array
	  ;; The box constraint for (MYROW,MYCOL) corresponds to
	  ;;   the 3*(floor myrow/3) + (floor mycol/3) row of
	  ;;   the *CS* array.
	  (setf (svref veck indy)
	    (list ;; The row constraint for MYROW corresponds to 
	          ;; row MYROW in the *CS* array
	          myrow
		  ;; The column constraint for MYCOL corresponds to
		  ;; row (+ 9 MYCOL) of the *CS* array
		  (+ 9 mycol) 
		  ;; The BOX constraint for (MYROW,MYCOL) corresponds to
		  ;; row (+ 18 (* 3 (floor (/ myrow 3))) (floor (/ mycol 3)))
		  ;; of the *CS* array.  
		  (+ 18 
		     (* 3 (floor (/ myrow 3))) 
		     (floor (/ mycol 3)))))))
      veck))

;;;  As promised, GET-CONSTRAINTS-INDICES can just return the 
;;;  corresponding entry from the *CONSTRAINT-INDICES* vector!

(defun get-constraint-indices (indy)
  (svref *constraint-indices* indy))

  
(defconstant *blank* '_)

(defparameter *num-nodes* 0)

;;;  Some sample SUDOKU puzzles (represented as lists-of-lists)

(defparameter *t1* 
    '((_ _ 2 _ 9 _ 1 _ 7)
      (_ 3 8 6 _ _ _ _ _)
      (4 _ _ _ _ _ _ _ _)
      (_ _ _ _ _ 5 _ _ _)
      (_ _ 9 _ 1 _ 3 _ _)
      (_ _ _ 4 _ _ _ _ _)
      (_ _ _ _ _ _ _ _ 4)
      (_ _ _ _ _ 7 9 2 _)
      (8 _ 6 _ 3 _ 7 _ _)))

(defparameter *t2* 
    '((_ _ 5 3 _ _ _ _ _)
      (8 _ _ _ _ _ _ 2 _)
      (_ 7 _ _ 1 _ 5 _ _)
      (4 _ _ _ _ 5 3 _ _)
      (_ 1 _ _ 7 _ _ _ 6)
      (_ _ 3 2 _ _ _ 8 _)
      (_ 6 _ 5 _ _ _ _ 9)
      (_ _ 4 _ _ _ _ 3 _)
      (_ _ _ _ _ 9 7 _ _)))

(defparameter *t3* 
    '((8 5 _ _ _ 2 4 _ _)
      (7 2 _ _ _ _ _ _ 9)
      (_ _ 4 _ _ _ _ _ _)
      (_ _ _ 1 _ 7 _ _ 2)
      (3 _ 5 _ _ _ 9 _ _)
      (_ 4 _ _ _ _ _ _ _)
      (_ _ _ _ 8 _ _ 7 _)
      (_ 1 7 _ _ _ _ _ _)
      (_ _ _ _ 3 6 _ 4 _)))

(defparameter *t4* 
    '((_ _ _ _ _ 3 _ 6 _)
      (_ _ _ _ _ _ _ 1 _)
      (_ 9 7 5 _ _ _ 8 _)
      (_ _ _ _ 9 _ 2 _ _)
      (_ _ 8 _ 7 _ 4 _ _)
      (_ _ 3 _ 6 _ _ _ _)
      (_ 1 _ _ _ 2 8 9 _)
      (_ 4 _ _ _ _ _ _ _)
      (_ 5 _ 1 _ _ _ _ _)))

(defparameter *t5* 
    '((_ _ 6 _ _ _ _ 9 _)
      (_ _ _ 5 _ 1 7 _ _)
      (2 _ _ 9 _ _ 3 _ _)
      (_ 7 _ _ 3 _ _ 5 _)
      (_ 2 _ _ 9 _ _ 6 _)
      (_ 4 _ _ 8 _ _ 2 _)
      (_ _ 1 _ _ 3 _ _ 4)
      (_ _ 5 2 _ 7 _ _ _)
      (_ 3 _ _ _ _ 8 _ _)))

(defparameter *t6* 
    '((_ _ _ 2 _ _ _ 6 3)
      (3 _ _ _ _ 5 4 _ 1)
      (_ _ 1 _ _ 3 9 8 _)
      (_ _ _ _ _ _ _ 9 _)
      (_ _ _ 5 3 8 _ _ _)
      (_ 3 _ _ _ _ _ _ _)
      (_ 2 6 3 _ _ 5 _ _)
      (5 _ 3 7 _ _ _ _ 8)
      (4 7 _ _ _ 1 _ _ _)))

(defparameter *t7* 
    '((1 _ _ _ 7 _ _ 3 _)
      (8 3 _ 6 _ _ _ _ _)
      (_ _ 2 9 _ _ 6 _ 8)
      (6 _ _ _ _ 4 9 _ 7)
      (_ 9 _ _ _ _ _ 5 _)
      (3 _ 7 5 _ _ _ _ 4)
      (2 _ 3 _ _ 9 1 _ _)
      (_ _ _ _ _ 2 _ 4 3)
      (_ 4 _ _ 8 _ _ _ 9)))

(defparameter *t8* 
    '((_ 2 _ _ _ _ _ _ 7)
      (_ 7 _ _ _ 4 _ 1 _)
      (9 _ 5 _ _ _ _ _ _)
      (_ 8 _ 6 3 _ _ _ 2)
      (7 _ _ _ _ _ _ _ 1)
      (2 _ _ _ 1 8 _ 6 _)
      (_ _ _ _ _ _ 4 _ 9)
      (_ 3 _ 1 _ _ _ 2 _)
      (4 _ _ _ _ _ _ 8 _)))

(defparameter *fails* 
    '((1 1 1 1 1 1 1 1 1)
      (1 1 1 1 1 1 1 1 1)
      (1 1 1 1 1 1 1 1 1)
      (1 1 1 1 1 1 1 1 1)
     (1 1 1 1 1 1 1 1 1)
      (1 1 1 1 1 1 1 1 1)
      (1 1 1 1 1 1 1 1 1)
     (1 1 1 1 1 1 1 1 1)
      (1 1 1 1 1 1 1 1 1)))

(defparameter *success* 
    '((1 2 3 4 5 6 7 8 9)
      (2 3 4 5 6 7 8 9 1)
      (3 4 5 6 7 8 9 1 2)
      (4 5 6 7 8 9 1 2 3)
      (5 6 7 8 9 1 2 3 4)
      (6 7 8 9 1 2 3 4 5)
      (7 8 9 1 2 3 4 5 6)
      (8 9 1 2 3 4 5 6 7 )
      (9 1 2 3 4 5 6 7 8)))

;;;  The GAME struct
;;; ------------------------------------------------------
;;;  Fields:
;;;     SLOTS  --  a vector of length 81, each element 
;;;                 representing one of the squares in a 9-by-9
;;;                 sudoku puzzle
;;;     DOMAINS -- a vector of length 81, each element being
;;;                 a list of at most 9 numbers that are potential
;;;                 values for the corresponding slot

(defstruct (game (:print-function print-game))
  (slots (make-array 81 :initial-element *blank*))
  (domains (make-array 81 :initial-element nil))
  )

;;;  PRINT-GAME
;;; ---------------------------------------------------------
;;;  INPUTS:  G, a GAME struct
;;;           STR, D -- ignored parameters
;;;  OUTPUT:  None
;;;  SIDE EFFECT:  Displays the sudoku game in the interactions window

(defun print-game (g str d)
  (declare (ignore d))
  (declare (ignore str))
  (dotimes (r 9)
    (dotimes (c 9)
      (format t "~A " (aref (game-slots g) (+ (* 9 r) c))))
    (format t "~%")))

;;;  GAME-COPY
;;; ------------------------------------------------------------
;;;  INPUT:  G, a GAME struct
;;;  OUTPUT:  A copy of the input GAME struct.  
;;;  NOTE:  The copy does not make copies of the domain lists.
;;;         Instead, it simply uses the *same* lists.  That's okay
;;;         because whenever we *reduce* the domains, we replace them
;;;         by new lists, we don't destructively modify the pre-existing
;;;         domain lists.  So, the output is a new GAME struct that
;;;         uses the same lists as the input GAME struct.

(defun game-copy (g)
  (let* ((newg (make-game))
	 (old-slots (game-slots g))
	 (old-doms (game-domains g))
	 (new-slots (game-slots newg))
	 (new-doms (game-domains newg)))
    ;; For each slot...
    (dotimes (i 81)
      (setf (aref new-slots i) (aref old-slots i))
      ;; See... we are *not* making copies of the domain lists,
      ;;  we are simply referring to the *same* lists.
      (setf (aref new-doms i) (aref old-doms i)))
    
    ;; Return the copy of the GAME struct
    newg))


;;;  INIT-GAME
;;; ----------------------------------------------------------
;;;  INPUT:  GRID, an optional list-of-lists representation of a sudoku puzzle
;;;  OUTPUT:  A GAME struct with the 81 slots initialized to the
;;;             values in the GRID, and the 81 domains initialized
;;;             to (1 2 3 4 5 6 7 8 9).

(defun init-game (&optional (grid nil))
  (let* ((g (make-game))
	 ;; The 81-element vector of domains 
	 (doms (game-domains g))
	 ;; The 81-element vector of slots
	 (slots (game-slots g)))
    ;; use the GRID if provided...
    (when grid
      ;; First, convert the list-of-lists GRID into a 9-by-9 array, HARRY
      (let ((harry (make-array '(9 9) :initial-contents grid)))
	;; Then walk through the 9-by-9 array...
	(dotimes (r 9)
	  (dotimes (c 9)
	    ;; Set the SLOT to the corresponding element of the
	    ;; 9-by-9 array
	    (setf (aref slots (+ (* 9 r) c))
	      (aref harry r c))))))
    ;; Initialize each domain to (1 2 3 4 5 6 7 8 9)
    (dotimes (i 81)
      (setf (aref doms i) (list 1 2 3 4 5 6 7 8 9)))
    ;; Return the GAME struct
    g))


;;;  SELECT-VAR
;;; -----------------------------------------------------
;;;  INPUTS:  G, sudoku GAME struct
;;;           USE-DEGREE?, a boolean 
;;;  OUTPUT:  An index i corresponding to a currently blank slot
;;;     having the smallest domain.  (Returns NIL if all slots are
;;;     filled.)
;;;  NOTE:  If USE-DEGREE? is T, it uses the DEGREE heuristic to
;;;         break ties.  

(defun select-var (g &key (use-degree? nil))
  (let (;; MIN-SIZE:  the size of the smallest domain found so far
	(min-size 10)
	;; INDIES:  a list of indices having MIN-SIZE elements in their domains
	(indies nil)
	;; SLOTS and DOMS:  the slots and domains fields
	(slots (game-slots g))
	(doms (game-domains g)))
    ;; For each index from 0 to 80...
    (dotimes (i 81)
      (cond
       ;; Case 1:  The Ith slot is currently blank and has a domain
       ;;          containing *fewer* than MIN-SIZE elements
       ((and (eq (aref slots i) *blank*)
	     (< (length (aref doms i)) min-size))
	;; Update MIN-SIZE
	(setf min-size (length (aref doms i)))
	;; I is the first index having the new MIN-SIZE number of elements
	;; in its domain
	(setf indies (list i)))
       ;; Case 2:  The Ith slot is currently blank and has a domain
       ;;          containing exactly MIN-SIZE elements
       ((and (eq (aref slots i) *blank*)
	     (= (length (aref doms i)) min-size))
	;; So, push I onto the list of indices 
	(push i indies))))
    
    ;; Okay, at this point we have a list of zero or more indices
    ;; all having the same, minimal number of elements in their domains
    
    (cond
     ;; Case 1:  We're supposed to use the DEGREE heuristic to break
     ;;          ties and INDIES contains at least 2 elements...
     ((and use-degree? (rest indies))
      ;; So.... we need to break a tie!
      ;; We want to find the variable (i.e., slot) that has the
      ;; most constraints on remaining variables...
      (let (;; MAX-CONSTR = max number of constraints that any
	    ;;  any index in INDIES (that we have seen so far) has
	    ;;  on remaining variables
	    (max-constr -1)
	    ;; INDY = the index having MAX-CONSTR constraints on
	    ;;  remaining variables
	    (indy nil))
	;; For each index I in INDIES...
	(dolist (i indies)
	  (let (;; ROWS = the constraints in *CS* that govern index I
		(rows (get-constraint-indices i))
		;; COUNTER = the number of other slots that these constraints
		;;           affect (starts off at zero)
		(counter 0)
		;; already seen indices
		already-seen)
	    ;; For each of the three constraints, R, that govern slot I...
	    (dolist (r rows)
	      ;; Look at the indices, C, governed by that constraint...
	      (dotimes (c 9)
		;; (aref *cs* r c) is an index into the SLOTS vector...
		;; If that index corresponds to a blank slot (other than I)
		(when (and (not (member (aref *cs* r c) already-seen))
                           (not (= i (aref *cs* r c)))
			   (eq (aref slots (aref *cs* r c)) *blank*))
		  ;; then increment the counter, because we found a 
		  ;; slot affected by I
		  (incf counter)
		  (push (aref *cs* r c) already-seen))))
	    ;; If slot I affected more remaining slots than previously found...
	    (when (> counter max-constr)
	      ;; Then update MAX-CONSTR
	      (setf max-constr counter)
	      ;; And I is our "best so far" index
	      (setf indy i))))
	;; Return the best index found (i.e., the one that constrains
	;; the most remaining variables)
	indy))
     
     ;; Case 2:  We don't need to use the DEGREE heuristic (either
     ;;  because USE-DEGREE? is NIL or INDIES contains fewer than 
     ;;  two elements)
     (t
      ;; Arbitrarily return the first element of INDIES...
      ;; NOTE:  If INDIES is NIL, then (FIRST INDIES) is NIL too...
      (first indies)
      ;; Alternatively, could return a randomly selected element
      ;; of INDIES:  (nth (random (length indies)) indies)
      ;; But this only works if INDIES is non-empty!
      ))))


;;; COLLECT-FORCED-MOVES
;;; ---------------------------------------
;;;  INPUT:  G, a sudoku GAME struct
;;;  OUTPUT:  A list of forced moves (e.g., the moves that are forced by the 
;;;     initial sudoku puzzle:  slots that already have a value can't be 
;;;     changed)

(defun collect-forced-moves (g)
  (let (;; FORCIES:  an accumulator
	(forcies nil)
	(slots (game-slots g)))
    (dotimes (i 81)
      ;; Any slot that already has a non-blank value
      (when (not (eq (aref slots i) *blank*))
	;; is a *forced* move...
	;; So push the pair (I VALUE) onto FORCIES
	(push (list i (aref slots i)) forcies)))
    ;; return the accumulated forced moves
    forcies))

;;;  SOLVE-WRAPPER
;;; ---------------------------------------------------------------
;;;  INPUTS:  G, a sudoku GAME struct
;;;           USE-DEGREE?, a boolean
;;;           USE-PROP?, a boolean
;;;  OUTPUT:  A solved sudoku puzzle (if possible) or NIL.
;;;  NOTE:  If USE-DEGREE? is T, it uses the DEGREE heuristic to break 
;;;         ties in SELECT-VAR.  Uses "forward checking" to reduce
;;;         domains whenever a slot is given a value.  (See REDUCE-DOMAINS!)
;;;         In addition, if USE-PROP? is T, it recursively processes
;;;         any "naked doubles" created by filling in some slot.  (See
;;;         REDUCE-DOMAINS-EXTRA!)

(defun solve-wrapper (g &key (use-degree? nil)
			     (use-prop? t))
  ;; *NUM-NODES* is incremented every time we create a new node (i.e., GAME)
  (setf *num-nodes* 0)
  (let (;; FORCIES:  the moves forced by the initial puzzle
	;;   Each element of FORCIES is an (INDEX VALUE) pair
	(forcies (collect-forced-moves g)))
    ;; do all the forced moves -- no backtracking!!
    (mapcar #'(lambda (forcie)
		(let* ((i (first forcie))
		       (val (second forcie))
		       ;; Use forward checking to reduce domains of
		       ;; remaining variables caused by assigning VAL
		       ;; to the Ith slot.  Note:  LISTY is a list of
		       ;; indices whose domains were reduced to exactly
		       ;; two elements (i.e., potential naked doubles)
		       (listy (reduce-domains! g i val)))
		  ;; If asked to, recursively process any naked doubles
		  ;; that arose from setting Ith slot to VAL
		  (when use-prop?
		    (reduce-domains-extra! g listy))))
	    forcies))
  
  ;; now try to solve the puzzle from here...
  (solve g 
	 :use-degree? use-degree?
	 :use-prop? use-prop?
	 ))

;;;  SCRAMBLE-LIST
;;; --------------------------------------------------
;;;  INPUT:  LISTY, a list
;;;  OUTPUT:  A list containing the same elements as LISTY, but
;;;           in a randomly scrambled order.
;;;  NOTE:  This function is provided for fun...

(defun scramble-list (listy)
  ;; Base Case:  LISTY is empty
  (if (null listy)
      ;; So return the empty list
      ()
    ;; Recursive Case:  LISTY is non-empty
    (let* ((len (length listy))
	   (rnd (random len))
	   (item (nth rnd listy)))
      ;; Cons a randomly selected ITEM onto the scrambling of the
      ;; remaining elements
      (cons item
	    (scramble-list (remove item listy :count 1))))))

;;;  SOLVE
;;; -------------------------------------
;;;  INPUT:  G, a sudoku game in which all initial forced moves have 
;;;              already been made
;;;  OUTPUT:  A solved puzzle (or NIL)

(defun solve (g &key (use-degree? nil) (use-prop? t))
  (incf *num-nodes*)
  (let (;; Select the slot to be assigned next
	(i (select-var g :use-degree? use-degree?))
	(doms (game-domains g)))
    (cond
     ;; Case 1:  G is already solved
     ((null i)
      (format t "Solved!")
      ;; return the solved puzzle
      g)
     
     ;; Case 2:  G is not yet solved!
     (t
      (let (;; DOM-I is the domain for the Ith slot
	    (dom-i (aref doms i)))
	(when
	 ;; No values left in this domain...
	 (null dom-i)
	 ;; Return FAILURE...
	 (return-from solve nil))
	
	;; Otherwise... walk through the possible domain values for this slot 
	(dolist (val dom-i) ;; Alternative:  Use (scramble-list dom-i))
	  (let* (;; CHILD-G is a new GAME struct in which the Ith
		 ;;  slot has been set to VAL
		 (child-g (do-move g i val))
		 ;; Use forward checking to reduce the domains of remaining
		 ;; variables in view of having set Ith slot to VAL...
		 ;; NOTE:  LISTY is a list of indices whose domains were
		 ;;        reduced to exactly two elements (i.e., potential
		 ;;        naked doubles).
		 (listy (reduce-domains! child-g i val)))
	    ;; If asked to, recursively process any naked doubles
	    ;; that arose from having set Ith slot to VAL
	    (when use-prop?
	      (reduce-domains-extra! child-g listy))
	    
	    (let (;; Recursively try to solve the resulting GAME...
		  (child-results (solve child-g 
					:use-degree? use-degree?
					:use-prop? use-prop?)))
	      ;; If we got a solution...
	      (when child-results
		;; yeah! immediately terminate this function call,
		;;  returning the solution we just found!
		(return-from solve child-results)))))

	;; If got here, then all recursive attempts failed to find
	;; a solution, so return NIL indicating failure (to our parent)
	(return-from solve nil))))))


;;;  DO-MOVE
;;; ------------------------------------------------
;;;  INPUTS:  G, a sudoku GAME struct
;;;           I, index of selected slot
;;;           VAL, value to write in Ith position
;;;  OUTPUT:  New GAME struct that is same as G, except that the
;;;           Ith slot has been set to VAL.

(defun do-move (g i val)
  (cond
   ;; Case 1:  The Ith slot is currently blank
   ((eq (aref (game-slots g) i) *blank*)
    (let (;; Create a copy of the game struct...
	  (child-g (game-copy g)))
      ;; Set the Ith slot to VAL
      (setf (aref (game-slots child-g) i) val)
      ;; Then return the new game struct
      child-g))
   ((equalp val '_)
    (setf (aref (game-slots g) i) val)
   g)
   ;; Case 2:  The Ith slot is already filled...
   (t
    ;; Ooops!
    (format t "Umm... Illegal move!~%")
    nil)))


;;;  REDUCE-DOMAINS!
;;; ---------------------------------------------
;;;  INPUTS:  G, Sudoku game
;;;           I, index of some slot
;;;           VAL, value at that slot
;;;  OUTPUTS:  List of indices whose domains were reduced to 
;;;            precisely two elements (potential naked double)
;;;  SIDE EFFECTS:  Removes VAL from domains of all slots 
;;;    in same row, column or box as I.  (See "forward checking".)

(defun reduce-domains! (g i val)
  (let ((doms (game-domains g))
	(slots (game-slots g))
	;; The slot I is governed by three constraints...
	;;  a row constraint, a column constraint and a box constraint...
	;;  the constraint-indices feed into *cs* arrays...
	(constraint-indices (get-constraint-indices i))
	;; LISTY: an accumulator
	(listy nil))

    ;; REMOVE VAL FROM DOMAINS OF SLOTS LINKED TO I...
    (dolist (constr-index constraint-indices)
      ;; for each constraint, walk through the 9 slots it governs
      (dotimes (c 9)
	;; II is the current slot being looked at
	(let ((ii (aref *cs* constr-index c)))
	  ;; if II != I and IIth slot is currently blank,
	  ;;  and VAL belongs to domain of IIth slot
	  (when (and (not (= ii i))
		     (eq (aref slots ii) *blank*)
		     (member val (aref doms ii)))
	    ;; then destructively remove VAL from domain of II
	    (setf (aref doms ii) 
	      (remove val (aref doms ii)))
	    ;; and, if a potential naked double, push ii onto list 
	    ;; of changelings
	    (when (= 2 (length (aref doms ii)))
	      (push ii listy))))))
    
    ;; return list of indices corresponding to potential new naked doubles
    listy))

;;;  REDUCE-DOMAINS-EXTRA!
;;; ------------------------------------------------------------------
;;;  INPUTS:  G, a sudoku GAME struct
;;;           LISTY, a list of indices corresponding to slots whose
;;;             domains were recently reduced to exactly two elements.
;;;  OUTPUT:  G, possibly destructively modified
;;;  SIDE EFFECT:  Any naked doubles arising from indices in LISTY
;;;      whose domains contain exactly two elements are recursively
;;;      processed.  That is, domains of slots linked to these naked
;;;      doubles are reduced.  (See discussion of "naked doubles" in
;;;      the text.)

(defun reduce-domains-extra! (g listy)
  (cond
   ;; Case 1:  LISTY is empty
   ((null listy)
    ;; we're done...
    t)
   
   ;; Case 2:  LISTY is non-empty... more work to do
   (t
    (let* (;; I = index to some slot whose domain was recently 
	   ;;     reduced to exactly two elements...
	   (i (first listy))
	   (theresty (rest listy))
	   (doms (game-domains g))
	   (slots (game-slots g))
	   ;; DOM-I:  the domain for slot I
	   (dom-i (aref doms i))
	   ;; The slot I is governed by three constraints...
	   ;;  a row constraint, a column constraint and a box constraint...
	   ;;  the constraint-indices feed into *cs* arrays...
	   (constraint-indices (get-constraint-indices i)))
      
      ;; NOTE:  The domain for slot I might have been reduced to a single
      ;;        element since we last looked at it.  If so, we don't 
      ;;        bother to process index I as part of a naked double
      ;;        because the Ith slot will be assigned its only remaining
      ;;        value soon enough and forward checking will take care
      ;;        of any needed domain reductions.
      (when (= (length dom-i) 2)
	(let (;; I-ONE and I-TWO are the two values in the 
	      ;; domain for slot I
	      (i-one (first dom-i))
	      (i-two (second dom-i)))
	  ;; For each constraint (i.e., ROW, COL or BOX) 
	  (dolist (constr-index constraint-indices)
	    ;; Walk through slots in that CONSTRAINT checking for
	    ;; any that have the SAME domain as this one.
	    (dotimes (c 9)
	      (let* (;; II = slot index
		     (ii (aref *cs* constr-index c))
		     ;; DOM-II = domain for slot II
		     (dom-ii (aref doms ii)))
		;; When II is a different slot from I, that is currently
		;; blank, and whose domain contains the same TWO elements
		;; as the domain for I...
		(when (and (not (= i ii))
			   (eq (aref slots ii) *blank*)
			   (= (length dom-ii) 2)
			   (member i-one dom-ii)
			   (member i-two dom-ii))
		  ;; ... then we can *remove* those elements from 
		  ;; the domain of any other slot in that same constraint
		  (dotimes (cc 9)
		    (let ((x (aref *cs* constr-index cc)))
		      ;; Only reduce X's domain if X is a blank slot that
		      ;; is not the Ith or IIth slot
		      (when (and (not (= x i))
				 (not (= x ii))
				 (eq (aref slots x) *blank*))
			(let ((x-dom (aref doms x)))
			  ;; If I-ONE appears in X's domain...
			  (when (member i-one x-dom)
			    ;; Remove it (destructively)
			    (setf (aref doms x) (remove i-one x-dom))
			    ;; And if X's domain now has 2 elements...
			    (when (and (= (length (aref doms x)) 2)
				       (not (member x theresty)))
			      ;; X might be part of a new naked double...
			      (push x theresty))))
			;; Same as above, but for second element of I's domain
			(let ((x-dom (aref doms x)))
			  (when (member i-two x-dom)
			    (setf (aref doms x) (remove i-two x-dom))
			    (when (and (= (length (aref doms x)) 2)
				       (not (member x theresty)))
			      (push x theresty)))))))))))))
      
      ;; Okay, now make recursive call on THERESTY...
      (reduce-domains-extra! g theresty)))))


;;; ==========================================
;;;  FUNCTIONS FOR TESTING THE SUDOKU SOLVER
;;; ==========================================

;;;  TESTY
;;; ---------------------------------------------
;;;  Apply the solver to *T1*

(defun testy ()
  (setf g (init-game *t1*))
  (let ((results (solve-wrapper g)))
    (format t "Num nodes: ~A~%" 
	    *num-nodes*)
    results))

;;;  SUD-ALL
;;; ----------------------------------------------
;;;  INPUT:  INIT-BOARD, a list-of-lists representation of a sudoku puzzle
;;;  OUTPUT:  none
;;;  SIDE-EFFECT:  Calls the sudoku solver four times, once for
;;;    each combination of the boolean flags, USE-DEGREE? and USE-PROP?,
;;;    on the puzzle INIT-BOARD.  Prints out results.

(defun sud-all (init-board)
  (setf g (init-game init-board))
  (dolist (keys '((nil nil) (nil t) (t nil) (t t)))
    (sud init-board :use-degree? (first keys)
	 :use-prop? (second keys))))

;;;  SUD
;;; ---------------------------------------------------------
;;;  INPUTS:  INIT-BOARD, a list-of-lists representation of a sudoku puzzle
;;;           USE-DEGREE?, a boolean
;;;           USE-PROP?, a boolean
;;;  OUTPUT:  The solved puzzle or NIL
;;;  NOTE:  Calls the solver, SOLVE-WRAPPER, with the input boolean flags.

(defun sud (init-board &key
		       (use-degree? nil)
		       (use-prop? t))
  (setf g (init-game init-board))
  (format t "USE-DEGREE? = ~A, USE-PROP? = ~A~%" use-degree? use-prop?)
  (let ((results (solve-wrapper g 
				:use-degree? use-degree?
				:use-prop? use-prop?)))
    (format t "Num nodes: ~A~%"
	    *num-nodes*)
    results))

;; NUM-OCCURANCES 
;; --------------------
;; INPUTS: LIST, A LIST OF INTEGERS
;;         NUM, AN INTEGER
;; OUTPUT: THE NUMBER OF OCCURANCES OF NUM IN LIST

(defun num-occurances (list num)
  (let ((occ 0))
    (dolist (numb list)
      (if (equalp numb num)
	  (setf occ (+ 1 occ))))
    occ))

;; CHECK-COL
;; --------------------
;; INPUTS: COL, AN INTEGER 0-8 INDICATING THE ROW TO BE CHECKED
;;         GAME, A SUDOKU GAME 
;; OUTPUT: T IF THE COL SATIFIES THE ALL DIFF CONSTRAINT
;;         NIL OTHERWISE 

(defun check-col (col game)
  (if (or (< col 0) (> col 8))
      (return-from check-col -100000))
  (let ((listy '())
	(tracky 0)
	(booly T))
    (setf tracky col)
    (dotimes (i 9)
      (setf listy (cons (aref (game-slots game) tracky) listy))
      (setf tracky (+ tracky 9)))
    (dotimes (j 9) 
      (if (> (num-occurances listy (+ 1 j)) 1)
	  (setf booly nil))
      (return-from check-col booly))))

;; CHECK-ROW
;; --------------------
;; INPUTS: ROW, AN INTEGER 0-8 INDICATING THE ROW TO BE CHECKED
;;         GAME, A SUDOKU GAME 
;; OUTPUT: T IF THE ROW SATIFIES THE ALL DIFF CONSTRAINT
;;         NIL OTHERWISE 

(defun check-row (row game)
  (if (or (< row 0) (> row 8))
      (return-from check-row -100000))
  (let ((listy '())
	(track T))
    (dotimes (i 9)
      (setf listy (cons (aref (game-slots game) (+ i (* row 9))) listy)))
    (dotimes (j 9) 
      (if (> (num-occurances listy (+ 1 j)) 1)
	  (setf track nil))
      (return-from check-row track))))

;; MAKE-HASH 
;; ---------------------
;; INPUT: NONE
;; OUTPUT: A HASHTABLE WITH 9 entries, where the key is used 
;;         to refrence a box number and the value is the starting 
;;         index of that box

(defun make-hash ()
  (setf hash (make-hash-table))
  (setf (gethash '0         hash     ) 0    )
  (setf (gethash '1         hash     ) 3    )
  (setf (gethash '2         hash     ) 6    )
  (setf (gethash '3         hash     ) 27   )
  (setf (gethash '4         hash     ) 30   )
  (setf (gethash '5         hash     ) 33   )
  (setf (gethash '6         hash     ) 54   )
  (setf (gethash '7         hash     ) 57   )
  (setf (gethash '8         hash     ) 60   )
  hash)

(defparameter *box-start* (make-hash ))

;; CHECK-BOX 
;; --------------------
;; INPUTS: GAME, A SUDOKU GAME 
;;         BOX, A INTEGER 0-9 INDICATING THE BOX NUMBER
;; OUTPUT: T IF THE BOX SATISIFIES THE ALL DIFF CONSTRAINT
;;           NIL OTHERWISE

(defun check-box (game box) 
  (if (or (< box 0) (> box 8)) 
      (return-from check-box -10000))
  (let ((listy '())
	(start (gethash box *box-start*))
	(booly T ))
    (dotimes (i 3)
      (setf listy (cons (aref (game-slots game) (+ start i)) listy)))
    (setf start (+ start 9))
    (dotimes (i 3)
      (setf listy (cons (aref (game-slots game) (+ start i)) listy)))
    (setf start (+ start 9))
    (dotimes (i 3)
      (setf listy (cons (aref (game-slots game) (+ start i)) listy)))
    (dotimes (j 9) 
      (if (> (num-occurances listy j) 1)
	  (setf booly nil)))
    (return-from check-box booly)))

;; CHECK-CONSTRAINTS 
;; -----------------------
;; INPUT: G, A SUDOKU GAME 
;; OUTPUT: T IF THE GAME SATISFIES ALL CONSTRAINTS
;;         ROW, COLUM, BOX AND NIL OTHERWISE 

(defun check-constraints (g)
  (let ((booly T))
    (dotimes (i 9)
      (if (not (and (and (check-row i g) (check-col i g)) (check-box g i)))
	  (setf booly nil)))
    (return-from check-constraints booly)))
    
;; HAS-EMPTY 
;;------------------------
;; INPUT: GAME, a sudoku game
;; OUTPUT: nil if there are no blank spaces
;;         or the index of the first blank space

(defun has-empty (game)
  (dotimes (i 81) 
    (if (equalp (aref (game-slots game) i) '_)
	(return-from has-empty i))))

;;; BACK-TRACK
;; -------------------
;; INPUT: G, A SUDOKU GAME 
;; OUTPUT: A SOLVED SUDOKU GAME
;; SIDE EFFECT: PRINTS NUMBERS OF STEPS TAKEN TO SOLVE GAME

(defun back-track (g)
  ;; find an unfilled cell
  (let ((idx (has-empty g)))
    (cond
     ;; no empty slots.. we have valid sudoku
     ;; return true
     ((not idx)
      (format t "~A" g)
      (return-from back-track T))
     (t
      ;; try values 1 - 9 in the empty slot
      (dotimes (j 9)
	;; if the value satifies constraints
        (if (check-constraints (do-move (copy-game g) idx (+ 1 j)))
	    ;; move is valid and do the move
            (progn
              (setf g (do-move g idx (+ 1 j)))
              (if (back-track g)
                  (return-from back-track T)))
	  ;; move is invalid.. try next value
	  ;; set the slot back to being empty
          (setf (aref (game-slots g) idx) '_)))
      ;; tried all possible values and none worked
      ;; return nil
      (return-from back-track nil)))))

