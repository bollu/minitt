(let
  zero [λ f (λ x x)]
  one [λ f (λ x ($ f x))]
  two [λ f (λ x ($ f ($ f x)))]
  church-add [λ i (λ j 
                   (λ f (λ x ($ ($ j f) ($ ($ i f) x)))))]
  ($ ($ church-add one) two))
