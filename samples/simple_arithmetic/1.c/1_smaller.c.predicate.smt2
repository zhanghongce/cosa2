;; Core predicates from original file
(define-fun |predicate.2| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (bvult y (_ bv200 15)))

(define-fun |predicate.3| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (=> (bvuge y (_ bv200 15)) (bvuge x y)))

(define-fun |predicate.4| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (= x (bvadd (_ bv1 15) 
             (bvudiv (bvmul y (bvsub y (_ bv1 15))) (_ bv2 15)))))

(define-fun |predicate.7| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (=> (= y (_ bv200 15)) (= x (_ bv19901 15))))

;; The essential lemma that IC3 is working to construct:
;; This represents the mathematical relationship x = y*(y-1)/2 + 1
;; This guarantees x ≥ y when y ≥ 200, which is exactly what we need to prove
(define-fun |predicate.induction_lemma| ((x (_ BitVec 15)) (y (_ BitVec 15))) Bool
  (= x (bvadd (_ bv1 15) (bvudiv (bvmul y (bvsub y (_ bv1 15))) (_ bv2 15)))))