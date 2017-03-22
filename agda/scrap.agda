((a ∧ b) ∧ (c ∧ d)) ∧ (e ∧ f) ⇒       
(a ∧ (b ∧ (c ∧ d))) ∧ (e ∧ f) ⇒  1st
(a ∧ ((b ∧ c) ∧ d)) ∧ (e ∧ f) ⇒  ⟹  
a ∧ (((b ∧ c) ∧ d) ∧ (e ∧ f)) ⇒
a ∧ ((b ∧ c) ∧ (d ∧ (e ∧ f))) ⇒
a ∧ ((b ∧ c) ∧ ((d ∧ e) ∧ f)) 


(a ∧ (b ∧ (c ∧ d))) ∧ (e ∧ f) ⇒  1st
(a ∧ ((b ∧ c) ∧ d)) ∧ (e ∧ f) ⇒  ⟹  
a ∧ (((b ∧ c) ∧ d) ∧ (e ∧ f)) ⇒
a ∧ ((b ∧ c) ∧ (d ∧ (e ∧ f))) ⇒
a ∧ ((b ∧ c) ∧ ((d ∧ e) ∧ f)) 

(pr trs do not interfere)

a ∧ ((b ∧ (c ∧ d)) ∧ (e ∧ f)) ⇒  1st 2nd
a ∧ (((b ∧ c) ∧ d) ∧ (e ∧ f)) ⇒  ⟹  
a ∧ ((b ∧ c) ∧ (d ∧ (e ∧ f))) ⇒
a ∧ ((b ∧ c) ∧ ((d ∧ e) ∧ f)) 

                                 1st 2nd
a ∧ (((b ∧ c) ∧ d) ∧ (e ∧ f)) ⇒  ⟹  
a ∧ ((b ∧ c) ∧ (d ∧ (e ∧ f))) ⇒    
a ∧ ((b ∧ c) ∧ ((d ∧ e) ∧ f)) ⇒

a ∧ ((b ∧ c) ∧ (d ∧ (e ∧ f))) ⇒ 1st 2nd 3rd 
a ∧ ((b ∧ c) ∧ ((d ∧ e) ∧ f))  ⟹  

a ∧ ((b ∧ c) ∧ ((d ∧ e) ∧ f)) 

----------------------------------

a ∧ ((b ∧ (c ∧ d)) ∧ (e ∧ f)) ⇒  1st 3rd  ---> This was not necessary.
a ∧ (((b ∧ c) ∧ d) ∧ (e ∧ f)) ⇒  ⟹  
a ∧ ((b ∧ c) ∧ (d ∧ (e ∧ f))) ⇒
a ∧ ((b ∧ c) ∧ ((d ∧ e) ∧ f)) 

a ∧ (((b ∧ (c ∧ d)) ∧ e) ∧ f) ⇒  1st 3rd 2nd
a ∧ ((((b ∧ c) ∧ d) ∧ e) ∧ f)  ⇒  ⟹  
a ∧ (((b ∧ c) ∧ (d ∧ e)) ∧ f)
a ∧ ((b ∧ c) ∧ ((d ∧ e) ∧ f))   --> Here we add a transformation

                                 1st 3rd 2nd

a ∧ (((b ∧ c) ∧ d) ∧ e) ∧ f)  ⇒  ⟹  
a ∧ (((b ∧ c) ∧ (d ∧ e)) ∧ f)
a ∧ ((b ∧ c) ∧ ((d ∧ e) ∧ f))

a ∧ (((b ∧ c) ∧ (d ∧ e)) ∧ f)
a ∧ ((b ∧ c) ∧ ((d ∧ e) ∧ f))

a ∧ ((b ∧ c) ∧ ((d ∧ e) ∧ f))

------------------------------------

((a ∧ b) ∧ (c ∧ d)) ∧ (e ∧ f) ⇒      
(a ∧ (b ∧ (c ∧ d))) ∧ (e ∧ f) ⇒  3rd
(a ∧ ((b ∧ c) ∧ d)) ∧ (e ∧ f) ⇒  ⟹  
a ∧ (((b ∧ c) ∧ d) ∧ (e ∧ f)) ⇒
a ∧ ((b ∧ c) ∧ (d ∧ (e ∧ f))) ⇒
a ∧ ((b ∧ c) ∧ ((d ∧ e) ∧ f)) 
