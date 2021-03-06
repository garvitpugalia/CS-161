;PAD(n) returns the summation of PAD(n-2) and PAD(n-3)
(defun PAD (x)
;Base cases for when PAD is called with 0,1,2
  (cond ((= x 0) 1)
	((= x 1) 1)
	((= x 2) 1)
	(t (+ (PAD (- x 2)) (PAD (- x 3))))))
;Recursively call for lower numbers and add the results

;SUMS(n) returns the number of additions used for a particular PAD call
(defun SUMS (x)
;For the base cases, the number of additions is zero
   (cond ((= x 0) 0)
	 ((= x 1) 0)
	 ((= x 2) 0)
	 (t (+ (SUMS (- x 2)) (SUMS (- x 3)) 1))))
;The number of additions is the number of additions for each value + 1 to add the two results

;ANON(x) returns an anonymized list with the same structure as x
(defun ANON (x)
;A null list will be returned for a null list
  (cond ((null x) '())
;Return just a question mark if the element is an atom
	((atom x) '?)
	(t (cons (ANON (car x)) (ANON (cdr x))))))
;Otherwise recursively convert each sublist into anonymous and merge the results
