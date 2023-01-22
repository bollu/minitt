;; toplevel definition of inductive, no indexes
(def-ind nat  []
  (zero []) ;; zero constructor
  (s nat []) ;; successor constructor
)

(zero-t (∈ (ind nat []) 0))
(three 
  (∈ (ind nat []) (mk s (mk s (mk s (mk zero)))))

(add (∈ (→ (ind nat []) (→ (ind nat []) (ind nat [])))
        (λ n (λ k (elim nat n
                       (λ n (ind nat []))
                       k
                       (λ add' (λ n' (mk s n'))))))))

(add1-zero (∈ nat (+1 0)))
(zero+_ ($ add 0))


(six (∈ nat
        ($ ($ add three) three)))

(id (∈ [→ nat nat] (λ x x)))
(ap-id-behind-lam (∈ [→ nat nat] (λ x ($ id x))))
