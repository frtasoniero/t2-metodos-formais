theory listas
  imports Main
begin

primrec cat::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
cat1:"cat [] l = l" |
cat2:"cat (h#T) l = h#(cat T l)"

theorem assoc:"\<forall>l2 l3 :: 'a list . cat l1 (cat l2 l3) = cat (cat l1 l2) l3"
proof (induction l1)
  show "\<forall>l2 l3 :: 'a list . cat [] (cat l2 l3) = cat (cat [] l2) l3"
  proof (rule allI, rule allI)
    fix l2::"'a list" and l3::"'a list"
    have "cat [] (cat l2 l3) = cat l2 l3" by (simp only:cat1)
    also have "... = cat (cat [] l2) l3" by (simp only:cat1)
    finally show "cat [] (cat l2 l3) = cat (cat [] l2) l3" by (simp)
  qed
next
  fix h::'a and l1::"'a list"
  assume HI:"\<forall>l2 l3 :: 'a list . cat l1 (cat l2 l3) = cat (cat l1 l2) l3"
  show "\<forall>l2 l3 :: 'a list . cat (h#l1) (cat l2 l3) = cat (cat (h#l1) l2) l3"
  proof (rule allI, rule allI)
    fix l2::"'a list" and l3::"'a list"
    have "cat (h#l1) (cat l2 l3) = h#(cat l1 (cat l2 l3))" by (simp only:cat2)
    also have "... = h#(cat (cat l1 l2) l3)" by (simp only:HI)
    also have "... = cat (h#(cat l1 l2)) l3" by (simp only:cat2)
    also have "... = cat (cat (h#l1) l2) l3" by (simp only:cat2)
    finally show "cat (h#l1) (cat l2 l3) = cat (cat (h#l1) l2) l3" by (simp)
  qed
qed
end