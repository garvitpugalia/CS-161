;;;;;;;;;;;;;;
; Homework 2 ;
;;;;;;;;;;;;;;

;;;;;;;;;;;;;;
; Question 1 ;
;;;;;;;;;;;;;;

; BFS: returns a list of elements in the list FRINGE traversed breadth-first
(defun BFS (FRINGE)
  (cond ((null FRINGE) '()) ;if FRINGE is an empty list, return NIL
	((atom FRINGE) FRINGE) ;if FRINGE is an atom/single element, return the element itself
	((listp (first FRINGE)) (BFS (append (cdr FRINGE) (first FRINGE))))
	;if the first element of FRINGE is a subtree, enqueue it's elements to the end of the list
	(t (cons (first FRINGE) (BFS (cdr FRINGE))))))
	;linearly traverse through the list, adding to the BFS result if the element is an atom

;As an example, here would be the steps implemented by the BFS for the list ((T (H R E) E)):

;((T (H R E) E)) -> ((H R E) E)       OUTPUT: T
;((H R E) E) -> (E H R E)             OUTPUT: T
;(E H R E) -> (H R E)                 OUTPUT: T E
;(H R E) -> (R E)                     OUTPUT: T E H
;...                                  OUTPUT: T E H R E

;;;;;;;;;;;;;;
; Question 2 ;
;;;;;;;;;;;;;;

; These functions implement a depth-first solver for the homer-baby-dog-poison
; problem. In this implementation, a state is represented by a single list
; (homer baby dog poison), where each variable is T if the respective entity is
; on the west side of the river, and NIL if it is on the east side.
; Thus, the initial state for this problem is (NIL NIL NIL NIL) (everybody 
; is on the east side) and the goal state is (T T T T).

; The main entry point for this solver is the function DFS, which is called
; with (a) the state to search from and (b) the path to this state. It returns
; the complete path from the initial state to the goal state: this path is a
; list of intermediate problem states. The first element of the path is the
; initial state and the last element is the goal state. Each intermediate state
; is the state that results from applying the appropriate operator to the
; preceding state. If there is no solution, DFS returns NIL.
; To call DFS to solve the original problem, one would call 
; (DFS '(NIL NIL NIL NIL) NIL) 
; However, it should be possible to call DFS with a different initial
; state or with an initial path.

; First, we define the helper functions of DFS.

; FINAL-STATE takes a single argument S, the current state, and returns T if it
; is the goal state (T T T T) and NIL otherwise.
(defun FINAL-STATE (S)
  (and (first S) (second S) (third S) (fourth S))) ;if S = (T T T T) -> the and of all elements must be true

; NEXT-STATE returns the state that results from applying an operator to the
; current state. It takes three arguments: the current state (S), and which entity
; to move (A, equal to h for homer only, b for homer with baby, d for homer 
; with dog, and p for homer with poison). 
; It returns a list containing the state that results from that move.
; If applying this operator results in an invalid state (because the dog and baby,
; or poisoin and baby are left unsupervised on one side of the river), or when the
; action is impossible (homer is not on the same side as the entity) it returns NIL.
; NOTE that next-state returns a list containing the successor state (which is
					; itself a list); the return should look something like ((NIL NIL T T)).
;first: homer, second: baby, third: dog, fourth: poison

(defun NEXT-STATE (S A)
  ;the first two conditions check if the current state S is legal
  (cond ((and (equal (second S) (third S)) (not (equal (second S) (first S)))) NIL) ;baby and dog cannot be alone on the same side
	((and (equal (second S) (fourth S)) (not (equal (second S) (first S)))) NIL) ;baby and poison cannot be alone on the same side
  ;the next four conditions check if the next state (corresponding to the move made) is illegal
	((and (equal A 'b) (not (equal (first S) (second S)))) NIL) ;if Homer is not on the same side as baby
	((and (equal A 'd) (or (not (equal (first S) (third S))) (equal (fourth S) (second S)))) NIL) ;if Homer is not on the same side as the dog, or moving the dog leaves the baby and poison alone
	((and (equal A 'p) (or (not (equal (first S) (fourth S))) (equal (second S) (third S)))) NIL) ;if Homer is not on the same side as the poison, or moving the poison leaves the baby and dog alone
	((and (equal A 'h) (or (and (equal (first S) (second S)) (equal (second S) (third S))) (and (equal (first S) (second S)) (equal (second S) (fourth S))))) NIL) ;if Homer moves, check for same conditions as above
  ;if all conditions are met, return a list representing the next state
	((equal A 'h) (list (list (not (first S)) (second S) (third S) (fourth S))))
	((equal A 'b) (list (list (not (first S)) (not (second S)) (third S) (fourth S))))
	((equal A 'd) (list (list (not (first S)) (second S) (not (third S)) (fourth S))))
	((equal A 'p) (list (list (not (first S)) (second S) (third S) (not (fourth S)))))
	(t NIL))) ;any other case, return NIL

; SUCC-FN returns all of the possible legal successor states to the current
; state. It takes a single argument (s), which encodes the current state, and
; returns a list of each state that can be reached by applying legal operators
; to the current state.
(defun SUCC-FN (S)
  (append (NEXT-STATE S 'p) (NEXT-STATE S 'd) (NEXT-STATE S 'b) (NEXT-STATE S 'h)))
  ;append all possible next states together using NEXT-STATE with all possible moves (ignores any NIL value returned) 

; ON-PATH checks whether the current state is on the stack of states visited by
; this depth-first search. It takes two arguments: the current state (S) and the
; stack of states visited by DFS (STATES). It returns T if s is a member of
; states and NIL otherwise.
(defun ON-PATH (S STATES)
  (cond ((null STATES) NIL) ;if the stack is empty, S is not a member, return false
	((equal S (car STATES)) t) ;if the front of the stack is S, return true
	(t (ON-PATH S (cdr STATES))))) ;tail-recursively traverse through the entire stack

; MULT-DFS is a helper function for DFS. It takes two arguments: a list of
; states from the initial state to the current state (PATH), and the legal
; successor states to the last, current state in the PATH (STATES). PATH is a
; first-in first-out list of states; that is, the first element is the initial
; state for the current search and the last element is the most recent state
; explored. MULT-DFS does a depth-first search on each element of STATES in
; turn. If any of those searches reaches the final state, MULT-DFS returns the
; complete path from the initial state to the goal state. Otherwise, it returns
; NIL.
(defun MULT-DFS (STATES PATH)
  (cond ((null STATES) NIL) ;if the potential legal moves are empty, return false
	((DFS (car STATES) PATH) (DFS (car STATES) PATH)) ;if DFS on the first state in the stack returns a solution, return this solution 
	(t (MULT-DFS (cdr STATES) PATH)))) ;else no solution exists for the current state, move on to the rest of legal moves and run MULT-DFS again

; DFS does a depth first search from a given state to the goal state. It
; takes two arguments: a state (S) and the path from the initial state to S
; (PATH). If S is the initial state in our search, PATH is set to NIL. DFS
; performs a depth-first search starting at the given state. It returns the path
; from the initial state to the goal state, if any, or NIL otherwise. DFS is
; responsible for checking if S is already the goal state, as well as for
; ensuring that the depth-first search does not revisit a node already on the
; search path.
(defun DFS (S PATH)
  (cond ((FINAL-STATE S) (append PATH (list S))) ;if the final state has been reached, add the final state
	;to the full PATH taken and return. For example: ((NIL NIL T T) (T T T T))
	((not (ON-PATH S PATH)) (MULT-DFS (SUCC-FN S) (append PATH (list S)))) ;else if the state has not been previously visited (i.e. not ON PATH),
	;run MULT-DFS on all potential next states (i.e. SUCC-FN) with the new path (including the current state appended)
	(t NIL))) ;else the state is already visited
