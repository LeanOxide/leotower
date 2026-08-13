import Lean

def demo_base : Nat := 21

theorem demo_thm : demo_base + demo_base = 42 := by
  native_decide

#check demo_thm
