;; Improved clauses for 1_smaller.c.v based on inductive proof
;; These clauses precisely capture the mathematical relationships between x and y

;; Clause 0: Main invariant - when y≥200, x must be ≥y (from the assertion)
(define-fun |clause.0| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (or (not (bvuge y (_ bv200 15)))
      (bvuge x y)))

;; Clause 1: Core invariant - The essential mathematical relationship x = 1 + y*(y-1)/2
;; This is the closed form solution derived through induction
(define-fun |clause.1| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (=> (bvult y (_ bv200 15))
      (= x (bvadd (_ bv1 15) 
              (bvudiv (bvmul y (bvsub y (_ bv1 15))) (_ bv2 15))))))

;; Clause 2: Base case - Initial state after reset
(define-fun |clause.2| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (or (not (= y (_ bv0 15))) 
      (= x (_ bv1 15))))

;; Clause 3: Terminal case - when y=200, x is exactly 19901 (from induction proof)
(define-fun |clause.3| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (=> (= y (_ bv200 15)) 
      (= x (_ bv19901 15))))

;; Clause 4: y is bounded by 200 (valid state constraint)
(define-fun |clause.4| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (bvule y (_ bv200 15)))

;; Clause 5: For all reachable states, x ≥ y when y ≥ 2
;; This directly follows from the formula x = 1 + y*(y-1)/2
(define-fun |clause.5| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (=> (and (bvuge y (_ bv2 15)) (bvule y (_ bv200 15)))
      (bvuge x y)))

;; Clause 6: For y=1, x must be exactly 1 (from induction basis)
(define-fun |clause.6| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (=> (= y (_ bv1 15)) 
      (= x (_ bv1 15))))

;; Clause 7: For all y≥200, x=19901 (terminal state)
(define-fun |clause.7| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (=> (bvuge y (_ bv200 15)) 
      (= x (_ bv19901 15))))

;; Clause 8: The formula x = 1 + y*(y-1)/2 implies x ≥ y for all y ≥ 1
(define-fun |clause.8| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (=> (and (bvuge y (_ bv1 15))
           (= x (bvadd (_ bv1 15) (bvudiv (bvmul y (bvsub y (_ bv1 15))) (_ bv2 15)))))
      (bvuge x y)))

;; Clause 9: Lower bound for x - x is always at least 1
(define-fun |clause.9| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (bvuge x (_ bv1 15)))

;; Clause 11: The invariant preserves state progression
(define-fun |clause.11| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (or (not (= x (bvadd (_ bv1 15) (bvudiv (bvmul y (bvsub y (_ bv1 15))) (_ bv2 15)))))
      (= (bvadd x y) (bvadd (_ bv1 15) (bvudiv (bvmul (bvadd y (_ bv1 15)) (bvsub (bvadd y (_ bv1 15)) (_ bv1 15))) (_ bv2 15))))))

()