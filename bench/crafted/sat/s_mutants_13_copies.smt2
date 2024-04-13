(set-logic HORN)
(declare-fun inv_0 (Int Int Int Int Int Int Int) Bool)
(declare-fun inv_1 (Int Int Int Int Int Int Int) Bool)
(declare-fun inv_2 (Int Int Int Int Int Int Int) Bool)
(declare-fun inv_3 (Int Int Int Int Int Int Int) Bool)
(declare-fun inv_4 (Int Int Int Int Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|_FH_2'| Int) (|_FH_3'| Int) (|_FH_4'| Int) (|_FH_5'| Int) (|count'| Int))
  (=>
    (and (= 1 |_FH_0'|) (= 1 |_FH_1'|) (= 1 |_FH_2'|) (= 1 |_FH_3'|) (= 1 |_FH_4'|) (= 1 |_FH_5'|) (= |count'| 0))
    (inv_0 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (count Int) (|count'| Int))
  (=>
    (and (= |_FH_0'| |_FH_1'|) (= |_FH_0'| |_FH_2'|) (= |_FH_0'| |_FH_3'|) (= |_FH_0'| |_FH_4'|) (= |_FH_0'| |_FH_5'|) (= |_FH_0'| (+ _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5)) (inv_0 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (< count 100) (= |count'| (+ count 1)))
    (inv_0 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int) (_FH_4 Int) (_FH_5 Int) (count Int))
  (=>
    (and (inv_0 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (>= count 100))
    (inv_1 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (count Int) (|count'| Int))
  (=>
    (and (= |_FH_0'| |_FH_1'|) (= |_FH_0'| |_FH_2'|) (= |_FH_0'| |_FH_3'|) (= |_FH_0'| |_FH_4'|) (= |_FH_0'| |_FH_5'|) (= |_FH_0'| (+ _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5)) (inv_1 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (< count 200) (= |count'| (+ count 1)))
    (inv_1 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int) (_FH_4 Int) (_FH_5 Int) (count Int))
  (=>
    (and (inv_1 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (>= count 200))
    (inv_2 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (count Int) (|count'| Int))
  (=>
    (and (= |_FH_0'| |_FH_1'|) (= |_FH_0'| |_FH_2'|) (= |_FH_0'| |_FH_3'|) (= |_FH_0'| |_FH_4'|) (= |_FH_0'| |_FH_5'|) (= |_FH_0'| (+ _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5)) (inv_2 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (< count 300) (= |count'| (+ count 1)))
    (inv_2 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int) (_FH_4 Int) (_FH_5 Int) (count Int))
  (=>
    (and (inv_2 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (>= count 300))
    (inv_3 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (count Int) (|count'| Int))
  (=>
    (and (= |_FH_0'| |_FH_1'|) (= |_FH_0'| |_FH_2'|) (= |_FH_0'| |_FH_3'|) (= |_FH_0'| |_FH_4'|) (= |_FH_0'| |_FH_5'|) (= |_FH_0'| (+ _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5)) (inv_3 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (< count 400) (= |count'| (+ count 1)))
    (inv_3 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int) (_FH_4 Int) (_FH_5 Int) (count Int))
  (=>
    (and (inv_3 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (>= count 400))
    (inv_4 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int) (_FH_4 Int) (|_FH_4'| Int) (_FH_5 Int) (|_FH_5'| Int) (count Int) (|count'| Int))
  (=>
    (and (= |_FH_0'| |_FH_1'|) (= |_FH_0'| |_FH_2'|) (= |_FH_0'| |_FH_3'|) (= |_FH_0'| |_FH_4'|) (= |_FH_0'| |_FH_5'|) (= |_FH_0'| (+ _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5)) (inv_4 count _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (< count 500) (= |count'| (+ count 1)))
    (inv_4 |count'| |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int) (_FH_4 Int) (_FH_5 Int) (count Int) (|count'| Int))
  (=>
    (and (distinct (+ _FH_0 _FH_1 _FH_2) (+ _FH_3 _FH_4 _FH_5)) (inv_4 |count'| _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (>= count 500))
    false)))

(check-sat)
