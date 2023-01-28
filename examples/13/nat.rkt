(ind nat []
  ((zero [] [])
   (succ [(k nat)] [])))

(ind vec [(x (ind nat [])) ]
  ((vzero [] [(ctor zero [])])
   (vsucc [(n nat) (v (ind vec [n]))] [(ctor succ [n])])))

(def z (ctor zero ()))
(def z2 (∈ (ind nat ()) (ctor zero ())))

(def o (ctor succ (ctor zero ())))
(def o2 (ctor succ (z)))
(def o3 (∈ (ind nat ()) (ctor succ (z))))


(def fact (∈ (-> nat nat) (l* [(x nat)] nat x)))


(def len (ctor succ (z)))

(def veczero (∈ (Π (k nat) (ind vec [k]))
  (l* [(n nat)] (ind vec [n])
     (elim nat n
        (l* [(p nat)] univ (ind vec [p]))
        (ctor vzero)
        (l* [(m nat) (vm (ind vec [m]))] nat (ctor asucc vm))))))
