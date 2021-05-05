(let Bool U
   (Sum [true 1] [false 1]))
(let elimBool (Π [C (→ Bool U)] 
                 (→ {$ C false}
                    (→ {$ C true} (Π [b Bool] {$ C b}))))
  (λ C (λ h0 (λ h1 
                 (fun [true h1]
                      [false h0])))))
                     
                 
