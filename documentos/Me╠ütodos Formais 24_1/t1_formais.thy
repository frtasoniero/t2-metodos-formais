txt"Trabalho 1 de Metodos Formais
Alunos: Alessandro Borges, Arthur Henz e Henrique Derlam"
theory t1_formais
  imports Main
begin

txt"Soma"

txt"Definicao do enunciado:"
primrec soma::"nat ⇒ nat ⇒ nat" where
soma01:"soma x 0 = x"|
soma02:"soma x (Suc y) = Suc (soma x y)"

lemma soma1:"∀x. soma x y = x + y"
proof (induct y)
  show "∀x. soma x 0 = x + 0"
  proof (rule allI)
    fix x0::nat
    have "soma x0 0 = x0" by (simp only:soma01)
    also have "... = x0 + 0" by simp
    finally show "soma x0 0 = x0 + 0" by simp
  qed
next
  fix y0::nat
  assume HI:"∀x. soma x y0 = x + y0"
  show "∀x. soma x (Suc y0) = x + (Suc y0)"
  proof (rule allI)
    fix x0::nat
    have "soma x0 (Suc y0) = Suc (soma x0 y0)" by (simp only:soma02)
    also have "... = Suc (x0 + y0)" by (simp only:HI)
    also have "... = x0 + (Suc y0)" by simp
    finally show "soma x0 (Suc y0) = x0 + (Suc y0)" by simp
  qed
qed

lemma soma2:"∀x. soma x y = soma y x"
proof (induct y)
  show "∀x. soma x 0 = soma 0 x"
  proof (rule allI)
    fix x0::nat
    have "soma x0 0 = x0" by (simp only:soma01)
    also have "... = 0 + x0" by simp
    also have "... = soma 0 x0" by (simp only:soma1)
    finally show "soma x0 0 = soma 0 x0" by simp
  qed
next
  fix y0::nat
  assume HI:"∀x. soma x y0 = soma y0 x"
  show "∀x. soma x (Suc y0) = soma (Suc y0) x"
  proof (rule allI)
    fix x0::nat
    have "soma x0 (Suc y0) = Suc (soma x0 y0)" by (simp only:soma02)
    also have "... = Suc (soma y0 x0)" by (simp only:HI)
    also  have "... = soma (Suc y0) x0" by (simp only:soma1)
    finally show "soma x0 (Suc y0) = soma (Suc y0) x0" by simp
  qed
qed

lemma soma3:"∀x. soma x (Suc y) = soma (Suc x) y"
proof (induct y)
  show "∀x. soma x (Suc 0) = soma (Suc x) 0"
  proof (rule allI)
    fix x0::nat
    have "soma x0 (Suc 0) = Suc (soma x0 0)" by (simp only:soma02)
    also have "... = Suc (x0)" by (simp only:soma01)
    also have "... = soma (Suc x0) 0" by (simp only:soma1)
    finally show "soma x0 (Suc 0) = soma (Suc x0) 0" by simp
  qed
next
  fix y0::nat
  assume HI:"∀x. soma x (Suc y0) = soma (Suc x) y0"
  show "∀x. soma x (Suc (Suc y0)) = soma (Suc x) (Suc y0)"
  proof (rule allI)
    fix x0::nat
    have "soma x0 (Suc (Suc y0)) = Suc (soma x0 (Suc y0))" by (simp only:soma02)
    also have "... = Suc (soma (Suc x0) y0)" by (simp only:HI)
    also have "... = soma (Suc x0) (Suc y0)" by (simp only:soma1)
    finally show "soma x0 (Suc (Suc y0)) = soma (Suc x0) (Suc y0)" by simp
  qed
qed

txt"Multiplicacao"

txt"Definicao do enunciado"

primrec mult::"nat ⇒ nat ⇒ nat" where
mult01:"mult x 0 = 0"|
mult02:"mult x (Suc y) = soma x (mult x y)"

lemma mult1:"∀x. mult x y = x * y"
proof (induct y)
  show "∀x. mult x 0 = x * 0"
  proof (rule allI)
    fix x0::nat
    have "mult x0 0 = 0" by (simp only:mult01)
    also have "... = x0 * 0" by simp
    finally show "mult x0 0 = x0 * 0" by simp
  qed
next
  fix y0::nat
  assume HI:"∀x. mult x y0 = x * y0"
  show "∀x. mult x (Suc y0) = x * (Suc y0)"
  proof (rule allI)
    fix x0::nat
    have "mult x0 (Suc y0) = soma x0 (mult x0 y0)" by (simp only:mult02)
    also have "... = soma x0 (x0 * y0)" by (simp only:HI)
    also have "... = soma (x0 * y0) x0" by (simp only:soma2)
    also have "... = (x0 * y0) + x0" by (simp only:soma1)
    also have "... = x0 * (Suc y0) + 0" by simp
    also have "... = soma (x0 * (Suc y0)) 0" by (simp only:soma1)
    also have "... = x0 * (Suc y0)" by (simp only:soma01)
    finally show "mult x0 (Suc y0) = x0 * (Suc y0)" by simp
  qed
qed

lemma mult2:"∀x. mult x y = mult y x"
proof (induct y)
  show "∀x. mult x 0 = mult 0 x"
  proof (rule allI)
    fix x0::nat
    have "mult x0 0 = 0" by (simp only:mult01)
    also have "... = 0*x0" by simp
    also have "... = 0*x0 + 0" by simp
    also have "... = (mult 0 x0) + 0" by (simp only:mult1)
    also have "... = soma (mult 0 x0) 0" by (simp only:soma1)
    also have "... = mult 0 x0" by (simp only:soma01)
    finally show "mult x0 0 = mult 0 x0" by simp
  qed
next
  fix y0::nat
  assume HI: "∀x. mult x y0 = mult y0 x"
  show "∀x. mult x (Suc y0) = mult (Suc y0) x"
  proof (rule allI)
    fix x0::nat
    have "mult x0 (Suc y0) = soma x0 (mult x0 y0)" by (simp only:mult02)
    also have "... = soma x0 (mult y0 x0)" by (simp only:HI)
    also have "... = soma x0 (y0 * x0)" by (simp only:mult1)
    also have "... = soma (y0 * x0) x0" by (simp only:soma2)
    also have "... = (y0 * x0) + x0" by (simp only:soma1)
    also have "... = (Suc y0) * x0 + 0" by simp
    also have "... = soma ((Suc y0) * x0) 0" by (simp only:soma1)
    also have "... = (Suc y0) * x0" by (simp only:soma01)
    also have "... = mult (Suc y0) x0" by (simp only:mult1)
    finally show "mult x0 (Suc y0) = mult (Suc y0) x0" by simp
  qed
qed

lemma mult3: "∀x. mult x 1 = x"
proof
  fix x
  show "mult x 1 = x"
  proof (induction x)
    case 0
    then show "mult 0 1 = 0" by (simp add: mult01)
  next
    case (Suc x)
    then have IH: "mult x 1 = x" by assumption
    have "mult (Suc x) 1 = soma (Suc x) (mult (Suc x) 0)" by (simp add: mult02)
    also have "... = soma (Suc x) 0" using IH by simp
    also have "... = Suc x" by (simp add: soma01)
    finally show "mult (Suc x) 1 = Suc x" by simp
  qed
qed

lemma mult4: "∀x. mult 1 x = x"
proof
  fix x
  show "mult 1 x = x"
  proof (induction x)
    case 0
    then show "mult 1 0 = 0" by (simp add: mult01)
  next
    case (Suc x)
    then have IH: "mult 1 x = x" by assumption
    have "mult 1 (Suc x) = soma 1 (mult 1 x)" by (simp add: mult02)
    also have "... = soma 1 x" using IH by simp
    also have "... = 1 + x" by (simp add: soma1)
    also have "... = Suc x" by simp
    finally show "mult 1 (Suc x) = Suc x" by simp
  qed
qed

end