(set-logic HORN)
(set-info :source |
  Benchmark: ../../sv-benchmarks/c/loops-crafted-1/multiloops/multiloop12.c
  Generated by Korn 0.4 https://github.com/gernst/korn
|)



(declare-fun $main_sum3 (Int Int Int) Bool)
(declare-fun $main_inv1 (Int Int Int) Bool)
(declare-fun $main_if3 (Int Int Int Int Int Int) Bool)
(declare-fun $main_inv3 (Int Int Int) Bool)
(declare-fun $main_if4 (Int Int Int Int Int Int) Bool)
(declare-fun $main_if5 (Int Int Int Int Int Int) Bool)
(declare-fun __VERIFIER_assert (Int) Bool)
(declare-fun $main_sum8 (Int Int Int) Bool)
(declare-fun $main_inv5 (Int Int Int) Bool)
(declare-fun $main_inv2 (Int Int Int) Bool)
(declare-fun $main_inv4 (Int Int Int) Bool)
(declare-fun $main_sum5 (Int Int Int) Bool)
(declare-fun $main_sum2 (Int Int Int) Bool)
(declare-fun $main_sum7 (Int Int Int) Bool)
(declare-fun $__VERIFIER_assert_pre (Int) Bool)
(declare-fun $__VERIFIER_assert_if1 (Int Int) Bool)
(declare-fun $main_sum1 (Int Int Int) Bool)
(declare-fun $main_sum6 (Int Int Int) Bool)
(declare-fun $main_if2 (Int Int Int Int Int Int) Bool)
(declare-fun $main_inv7 (Int Int Int) Bool)
(declare-fun $main_inv6 (Int Int Int) Bool)
(declare-fun $main_inv8 (Int Int Int) Bool)
(declare-fun $__VERIFIER_assert_ERROR (Int Int) Bool)
(declare-fun $main_sum4 (Int Int Int) Bool)

; label ERROR
(assert
  (forall ((cond!1 Int))
    (=> (and (not (not (= cond!1 0)))
             ($__VERIFIER_assert_pre cond!1))
        ($__VERIFIER_assert_ERROR cond!1 cond!1))))

; error
(assert
  (forall ((cond!1 Int) (cond!2 Int))
    (=> (and ($__VERIFIER_assert_ERROR cond!1 cond!2))
        false)))

; if else
(assert
  (forall ((cond!1 Int))
    (=> (and (not (not (not (= cond!1 0))))
             ($__VERIFIER_assert_pre cond!1))
        ($__VERIFIER_assert_if1 cond!1 cond!1))))

; post __VERIFIER_assert
(assert
  (forall ((cond!1 Int) (cond!3 Int))
    (=> (and ($__VERIFIER_assert_if1 cond!1 cond!3))
        (__VERIFIER_assert cond!1))))

; loop entry $main_inv1 (line 10)
(assert
  (forall ((y!5 Int) (z!6 Int) (x!4 Int))
    (=> (and (= z!6 0)
             (= y!5 100)
             (= x!4 0))
        ($main_inv1 0 y!5 z!6))))

; loop term $main_sum1 (line 10)
(assert
  (forall ((x!7 Int) (y!8 Int) (z!9 Int))
    (=> (and (not (< y!8 1000))
             ($main_inv1 x!7 y!8 z!9))
        ($main_sum1 x!7 y!8 z!9))))

; if then
(assert
  (forall ((x!7 Int) (y!8 Int) (z!9 Int))
    (=> (and (< x!7 500)
             (< y!8 1000)
             ($main_inv1 x!7 y!8 z!9))
        ($main_if2 x!7 y!8 z!9 (+ x!7 10) y!8 z!9))))

; if else
(assert
  (forall ((x!7 Int) (y!8 Int) (z!9 Int))
    (=> (and (not (< x!7 500))
             (< y!8 1000)
             ($main_inv1 x!7 y!8 z!9))
        ($main_if2 x!7 y!8 z!9 (- x!7 13) (+ y!8 40) z!9))))

; forwards $main_inv1 (line 10)
(assert
  (forall ((x!10 Int) (y!11 Int) (x!7 Int) (z!9 Int) (z!12 Int) (y!8 Int))
    (=> (and ($main_if2 x!7 y!8 z!9 x!10 y!11 z!12))
        ($main_inv1 x!10 y!11 z!12))))

; loop entry $main_inv2 (line 20)
(assert
  (forall ((x!13 Int) (y!14 Int) (z!15 Int))
    (=> (and (<= y!14 1000000)
             ($main_sum1 x!13 y!14 z!15))
        ($main_inv2 x!13 y!14 z!15))))

; loop term $main_sum2 (line 20)
(assert
  (forall ((x!16 Int) (y!17 Int) (z!18 Int))
    (=> (and (not (> y!17 z!18))
             ($main_inv2 x!16 y!17 z!18))
        ($main_sum2 x!16 y!17 z!18))))

; forwards $main_inv2 (line 20)
(assert
  (forall ((x!16 Int) (y!17 Int) (z!18 Int))
    (=> (and (> y!17 z!18)
             ($main_inv2 x!16 y!17 z!18))
        ($main_inv2 (+ x!16 1) (+ y!17 1) (+ z!18 100)))))

; loop entry $main_inv3 (line 26)
(assert
  (forall ((x!19 Int) (y!20 Int) (z!21 Int))
    (=> (and (<= y!20 x!19)
             ($main_sum2 x!19 y!20 z!21))
        ($main_inv3 x!19 y!20 z!21))))

; loop term $main_sum3 (line 26)
(assert
  (forall ((x!22 Int) (y!23 Int) (z!24 Int))
    (=> (and (not (>= y!23 500))
             ($main_inv3 x!22 y!23 z!24))
        ($main_sum3 x!22 y!23 z!24))))

; forwards $main_inv3 (line 26)
(assert
  (forall ((x!22 Int) (y!23 Int) (z!24 Int))
    (=> (and (>= y!23 500)
             ($main_inv3 x!22 y!23 z!24))
        ($main_inv3 x!22 (- y!23 200) (- z!24 10)))))

; loop entry $main_inv4 (line 31)
(assert
  (forall ((x!19 Int) (y!20 Int) (z!21 Int))
    (=> (and (not (<= y!20 x!19))
             ($main_sum2 x!19 y!20 z!21))
        ($main_inv4 x!19 y!20 z!21))))

; loop term $main_sum4 (line 31)
(assert
  (forall ((x!28 Int) (y!29 Int) (z!30 Int))
    (=> (and (not (>= x!28 250))
             ($main_inv4 x!28 y!29 z!30))
        ($main_sum4 x!28 y!29 z!30))))

; forwards $main_inv4 (line 31)
(assert
  (forall ((x!28 Int) (y!29 Int) (z!30 Int))
    (=> (and (>= x!28 250)
             ($main_inv4 x!28 y!29 z!30))
        ($main_inv4 (- x!28 200) y!29 (+ z!30 10)))))

; if then
(assert
  (forall ((y!26 Int) (x!4 Int) (z!27 Int) (y!5 Int) (x!25 Int) (z!6 Int))
    (=> (and ($main_sum3 x!25 y!26 z!27))
        ($main_if3 x!4 y!5 z!6 x!25 y!26 z!27))))

; if else
(assert
  (forall ((x!4 Int) (y!5 Int) (y!32 Int) (x!31 Int) (z!33 Int) (z!6 Int))
    (=> (and ($main_sum4 x!31 y!32 z!33))
        ($main_if3 x!4 y!5 z!6 x!31 y!32 z!33))))

; loop entry $main_inv5 (line 38)
(assert
  (forall ((x!13 Int) (y!14 Int) (z!15 Int))
    (=> (and (not (<= y!14 1000000))
             ($main_sum1 x!13 y!14 z!15))
        ($main_inv5 x!13 y!14 z!15))))

; loop term $main_sum5 (line 38)
(assert
  (forall ((x!37 Int) (y!38 Int) (z!39 Int))
    (=> (and (not (> y!38 z!39))
             ($main_inv5 x!37 y!38 z!39))
        ($main_sum5 x!37 y!38 z!39))))

; forwards $main_inv5 (line 38)
(assert
  (forall ((x!37 Int) (y!38 Int) (z!39 Int))
    (=> (and (> y!38 z!39)
             ($main_inv5 x!37 y!38 z!39))
        ($main_inv5 x!37 (- y!38 10) (+ z!39 15)))))

; loop entry $main_inv6 (line 43)
(assert
  (forall ((x!40 Int) (y!41 Int) (z!42 Int))
    (=> (and (<= y!41 x!40)
             ($main_sum5 x!40 y!41 z!42))
        ($main_inv6 x!40 y!41 z!42))))

; loop term $main_sum6 (line 43)
(assert
  (forall ((x!43 Int) (y!44 Int) (z!45 Int))
    (=> (and (not (>= y!44 500))
             ($main_inv6 x!43 y!44 z!45))
        ($main_sum6 x!43 y!44 z!45))))

; forwards $main_inv6 (line 43)
(assert
  (forall ((x!43 Int) (y!44 Int) (z!45 Int))
    (=> (and (>= y!44 500)
             ($main_inv6 x!43 y!44 z!45))
        ($main_inv6 x!43 (- y!44 200) (- z!45 10)))))

; loop entry $main_inv7 (line 48)
(assert
  (forall ((x!40 Int) (y!41 Int) (z!42 Int))
    (=> (and (not (<= y!41 x!40))
             ($main_sum5 x!40 y!41 z!42))
        ($main_inv7 x!40 y!41 z!42))))

; loop term $main_sum7 (line 48)
(assert
  (forall ((x!49 Int) (y!50 Int) (z!51 Int))
    (=> (and (not (>= x!49 250))
             ($main_inv7 x!49 y!50 z!51))
        ($main_sum7 x!49 y!50 z!51))))

; forwards $main_inv7 (line 48)
(assert
  (forall ((x!49 Int) (y!50 Int) (z!51 Int))
    (=> (and (>= x!49 250)
             ($main_inv7 x!49 y!50 z!51))
        ($main_inv7 (- x!49 200) y!50 (+ z!51 10)))))

; if then
(assert
  (forall ((y!47 Int) (x!4 Int) (y!5 Int) (x!46 Int) (z!48 Int) (z!6 Int))
    (=> (and ($main_sum6 x!46 y!47 z!48))
        ($main_if4 x!4 y!5 z!6 x!46 y!47 z!48))))

; if else
(assert
  (forall ((y!53 Int) (x!4 Int) (y!5 Int) (x!52 Int) (z!6 Int) (z!54 Int))
    (=> (and ($main_sum7 x!52 y!53 z!54))
        ($main_if4 x!4 y!5 z!6 x!52 y!53 z!54))))

; if then
(assert
  (forall ((x!34 Int) (x!4 Int) (y!5 Int) (y!35 Int) (z!36 Int) (z!6 Int))
    (=> (and ($main_if3 x!4 y!5 z!6 x!34 y!35 z!36))
        ($main_if5 x!4 y!5 z!6 x!34 y!35 z!36))))

; if else
(assert
  (forall ((x!4 Int) (y!5 Int) (y!56 Int) (z!57 Int) (z!6 Int) (x!55 Int))
    (=> (and ($main_if4 x!4 y!5 z!6 x!55 y!56 z!57))
        ($main_if5 x!4 y!5 z!6 x!55 y!56 z!57))))

; loop entry $main_inv8 (line 55)
(assert
  (forall ((x!4 Int) (y!5 Int) (z!60 Int) (y!59 Int) (z!6 Int) (x!58 Int))
    (=> (and ($main_if5 x!4 y!5 z!6 x!58 y!59 z!60))
        ($main_inv8 x!58 y!59 z!60))))

; loop term $main_sum8 (line 55)
(assert
  (forall ((x!61 Int) (y!62 Int) (z!63 Int))
    (=> (and (not (< x!61 z!63))
             ($main_inv8 x!61 y!62 z!63))
        ($main_sum8 x!61 y!62 z!63))))

; forwards $main_inv8 (line 55)
(assert
  (forall ((x!61 Int) (y!62 Int) (z!63 Int))
    (=> (and (< x!61 z!63)
             ($main_inv8 x!61 y!62 z!63))
        ($main_inv8 (- x!61 100) y!62 z!63))))

; pre __VERIFIER_assert
(assert
  (forall ((x!64 Int) (z!66 Int) (y!65 Int))
    (=> (and ($main_sum8 x!64 y!65 z!66))
        ($__VERIFIER_assert_pre (ite (= x!64 z!66) 1 0)))))

(check-sat)
