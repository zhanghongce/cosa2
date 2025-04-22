;; Improved helper predicates for 1_smaller.c.v
;; These predicates capture the precise mathematical relationship between x and y

;; Base case: After reset, x=1 and y=0
(define-fun |predicate.base_case| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (and (= x (_ bv1 15)) (= y (_ bv0 15))))

;; The invariant that holds for all reachable states where 0 ≤ y < 200:
;; x = 1 + y(y-1)/2
;; This is the closed-form formula derived from the inductive proof
(define-fun |predicate.invariant| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (=> (bvult y (_ bv200 15))
      (= x (bvadd (_ bv1 15) 
                 (bvudiv (bvmul y (bvsub y (_ bv1 15))) (_ bv2 15))))))

;; Terminal case: When y reaches 200, x = 19901 and registers freeze
(define-fun |predicate.terminal_case| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (=> (= y (_ bv200 15)) 
      (= x (_ bv19901 15))))

;; The complete inductive invariant that combines all cases
(define-fun |predicate.complete_invariant| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (or 
    ;; Base case after reset
    (and (= x (_ bv1 15)) (= y (_ bv0 15)))
    
    ;; The invariant during accumulation (0 < y < 200)
    (and (bvult y (_ bv200 15))
         (= x (bvadd (_ bv1 15) 
                    (bvudiv (bvmul y (bvsub y (_ bv1 15))) (_ bv2 15)))))
    
    ;; Terminal case when y = 200
    (and (= y (_ bv200 15)) 
         (= x (_ bv19901 15)))
    
    ;; Extra case for y > 200 (shouldn't occur in valid traces but included for completeness)
    (and (bvugt y (_ bv200 15))
         (= x (_ bv19901 15))
         (= y (_ bv200 15)))
  ))

;; This predicate directly proves the assertion
(define-fun |predicate.proves_assertion| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (=> (bvuge y (_ bv200 15))
      (bvuge x y)))

;; This shows how the invariant implies the assertion
(define-fun |predicate.invariant_implies_assertion| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (=> (|predicate.complete_invariant| x y)
      (|predicate.proves_assertion| x y)))

