import Mathlib

namespace PEqualNP.Outside

theorem L_goldbach_unit_anti_range :
    ∀ n a b : ℕ, 0<a → a<n → 0<b → b<n → (n ∣ a+b ↔ a+b=n) := by
  intro n a b ha han hb hbn
  constructor
  · intro h
    have hlo := Nat.le_of_dvd (show 0 < a + b by omega) h
    by_cases hpos : 0 < a + b - n
    · have hnext := Nat.le_of_dvd hpos (Nat.dvd_sub h (Nat.dvd_refl n))
      omega
    · omega
  · intro h
    simpa only [h] using (Nat.dvd_refl n)

end PEqualNP.Outside
