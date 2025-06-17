theory arvores
  imports Main
begin

datatype 'a ArvBin = ArvVazia | Nodo "'a ArvBin" 'a "'a ArvBin"

primrec espelho :: "'a ArvBin \<Rightarrow> 'a ArvBin" where
arv1:"espelho ArvVazia = ArvVazia" |
arv2:"espelho (Nodo e x d) = Nodo (espelho d) x (espelho e)"

theorem esp:"espelho (espelho a) = a"
proof (induct a)
  show "espelho (espelho ArvVazia) = ArvVazia"
  proof -
    have "espelho (espelho ArvVazia) = espelho ArvVazia" by (simp only:arv1)
    also have "... = ArvVazia" by (simp only:arv1)
    finally show "espelho (espelho ArvVazia) = ArvVazia" by (simp)
  qed
next
  fix e::"'a ArvBin" and d::"'a ArvBin" and x::"'a"
  assume HI1:"espelho (espelho e) = e"
  assume HI2:"espelho (espelho d) = d"
  show "espelho (espelho (Nodo e x d)) = Nodo e x d"
  proof -
    have "espelho (espelho (Nodo e x d)) = espelho (Nodo (espelho d) x (espelho e))" by (simp only:arv2)
    also have "... = Nodo (espelho (espelho e)) x (espelho (espelho d))" by (simp only:arv2)
    also have "... = Nodo e x (espelho (espelho d))" by (simp only:HI1)
    also have "... = Nodo e x d" by (simp only:HI2)
    finally show "espelho (espelho (Nodo e x d)) = Nodo e x d" by (simp)
  qed
qed
end