import Tatami.Mangle
namespace Tatami

theorem toNat_ofNat {n : Nat} (h : n.isValidChar) : (Char.ofNat n).toNat = n := by
  simp [Char.ofNat, dif_pos h, Char.toNat, Char.ofNatAux]

theorem lt_128_valid {n : Nat} (h : n < 128) : n.isValidChar := Or.inl (by omega)

theorem passesThrough_lt {b : UInt8} (h : passesThrough b = true) : b.toNat < 128 := by
  unfold passesThrough at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  omega

theorem toNat_ofNat_pass {b : UInt8} (h : passesThrough b = true) :
    (Char.ofNat b.toNat).toNat = b.toNat :=
  toNat_ofNat (lt_128_valid (passesThrough_lt h))

theorem pass_ne_underscore {b : UInt8} (h : passesThrough b = true) :
    Char.ofNat b.toNat ≠ '_' := by
  intro heq
  have h1 := toNat_ofNat_pass h
  rw [heq] at h1
  have h2 : ('_').toNat = 95 := by decide
  rw [h2] at h1
  unfold passesThrough at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  omega

/-- Inverse of `hexDigit` on `0..15`. What it does elsewhere does not matter:
    injectivity follows from the retraction alone. -/
def hexVal (c : Char) : Option Nat :=
  let k := c.toNat
  if 48 ≤ k && k ≤ 57 then some (k - 48)
  else if 97 ≤ k && k ≤ 102 then some (k - 87)
  else none

theorem hexVal_hexDigit {n : Nat} (h : n < 16) : hexVal (hexDigit n) = some n := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8
       ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem hexDigit_ne_underscore {n : Nat} (h : n < 16) : hexDigit n ≠ '_' := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8
       ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem toNat_lt_256 (b : UInt8) : b.toNat < 256 := by
  have h := UInt8.toNat_lt_size b
  have : UInt8.size = 256 := by rfl
  omega

theorem toNat_inj {a b : UInt8} (h : a.toNat = b.toNat) : a = b := by
  have e : UInt8.ofNat a.toNat = UInt8.ofNat b.toNat := by rw [h]
  rwa [UInt8.ofNat_toNat, UInt8.ofNat_toNat] at e

/-- hexDigit is injective on 0..15, read off its inverse. -/
theorem hexDigit_inj {m n : Nat} (hm : m < 16) (hn : n < 16)
    (h : hexDigit m = hexDigit n) : m = n := by
  have hv := hexVal_hexDigit hm
  rw [h, hexVal_hexDigit hn] at hv
  exact (Option.some_inj.mp hv).symm

theorem encodeByte_ne_nil (b : UInt8) : encodeByte b ≠ [] := by
  unfold encodeByte; split <;> simp

/-- The encoding is prefix-free: reading one byte off the front determines
    both the byte and what follows. This is what makes the concatenation
    injective, and it is where escaping the underscore earns its keep -- a
    pass-through character is never an underscore, and neither is a hex
    digit. -/
theorem encodeByte_append_inj {b1 b2 : UInt8} {t1 t2 : List Char}
    (h : encodeByte b1 ++ t1 = encodeByte b2 ++ t2) : b1 = b2 ∧ t1 = t2 := by
  have e1 : passesThrough b1 = true → encodeByte b1 = [Char.ofNat b1.toNat] :=
    fun hp => by simp [encodeByte, hp]
  have e2 : passesThrough b1 ≠ true →
      encodeByte b1 = ['_', hexDigit (b1.toNat / 16), hexDigit (b1.toNat % 16)] :=
    fun hp => by simp [encodeByte, hp]
  have f1 : passesThrough b2 = true → encodeByte b2 = [Char.ofNat b2.toNat] :=
    fun hp => by simp [encodeByte, hp]
  have f2 : passesThrough b2 ≠ true →
      encodeByte b2 = ['_', hexDigit (b2.toNat / 16), hexDigit (b2.toNat % 16)] :=
    fun hp => by simp [encodeByte, hp]
  by_cases h1 : passesThrough b1 = true <;> by_cases h2 : passesThrough b2 = true
  . rw [e1 h1, f1 h2] at h
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    refine ⟨toNat_inj ?_, h.2⟩
    rw [← toNat_ofNat_pass h1, ← toNat_ofNat_pass h2, h.1]
  . rw [e1 h1, f2 h2] at h
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact absurd h.1 (pass_ne_underscore h1)
  . rw [e2 h1, f1 h2] at h
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact absurd h.1.symm (pass_ne_underscore h2)
  . rw [e2 h1, f2 h2] at h
    simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
    have hb1 := toNat_lt_256 b1
    have hb2 := toNat_lt_256 b2
    have hd : b1.toNat / 16 = b2.toNat / 16 := hexDigit_inj (by omega) (by omega) h.1
    have hm : b1.toNat % 16 = b2.toNat % 16 := hexDigit_inj (by omega) (by omega) h.2.1
    exact ⟨toNat_inj (by omega), h.2.2⟩

theorem encodeBytes_eq_nil {bs : List UInt8} (h : encodeBytes bs = []) : bs = [] := by
  cases bs with
  | nil => rfl
  | cons b bs =>
      simp only [encodeBytes] at h
      exact absurd (List.append_eq_nil_iff.mp h).1 (encodeByte_ne_nil b)

theorem encodeBytes_injective : ∀ {a b : List UInt8}, encodeBytes a = encodeBytes b → a = b
  | [], [], _ => rfl
  | [], b :: bs, h => by
      have e : encodeBytes (b :: bs) = [] := h.symm
      exact absurd (encodeBytes_eq_nil e) (by simp)
  | a :: as, [], h => by
      have e : encodeBytes (a :: as) = [] := h
      exact absurd (encodeBytes_eq_nil e) (by simp)
  | a :: as, b :: bs, h => by
      simp only [encodeBytes] at h
      obtain ⟨rfl, ht⟩ := encodeByte_append_inj h
      rw [encodeBytes_injective ht]


/-! ### What a core cannot look like

The three shapes the outer layers must not collide with. All three are the
same head-stripping induction: a core's first character comes from a byte,
and which byte it was is visible from whether that character is `_`. -/

theorem encodeBytes_ne_underscore2 (bs : List UInt8) (t : List Char) :
    encodeBytes bs ≠ '_' :: '_' :: t := by
  intro h
  cases bs with
  | nil => simp [encodeBytes] at h
  | cons b bs' =>
      simp only [encodeBytes] at h
      by_cases hp : passesThrough b = true
      · rw [show encodeByte b = [Char.ofNat b.toNat] from by simp [encodeByte, hp]] at h
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
        exact absurd h.1 (pass_ne_underscore hp)
      · rw [show encodeByte b = ['_', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]
              from by simp [encodeByte, hp]] at h
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
        have hb := toNat_lt_256 b
        exact absurd h.2.1 (hexDigit_ne_underscore (show b.toNat / 16 < 16 by omega))

theorem encodeBytes_ne_f2 (bs : List UInt8) (t : List Char) :
    encodeBytes bs ≠ 'f' :: '_' :: '_' :: t := by
  intro h
  cases bs with
  | nil => simp [encodeBytes] at h
  | cons b bs' =>
      simp only [encodeBytes] at h
      by_cases hp : passesThrough b = true
      · rw [show encodeByte b = [Char.ofNat b.toNat] from by simp [encodeByte, hp]] at h
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
        exact absurd h.2 (encodeBytes_ne_underscore2 bs' t)
      · rw [show encodeByte b = ['_', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]
              from by simp [encodeByte, hp]] at h
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
        simp at h

/-- No core ends in `_`: an underscore is always followed by two hex digits.
    Induction on the prefix, which is possible because a keyword contains no
    underscore, so every one of its characters must have passed through. -/
theorem encodeBytes_ne_snoc_underscore :
    ∀ (p : List Char), (∀ c ∈ p, c ≠ '_') →
      ∀ (bs : List UInt8), encodeBytes bs ≠ p ++ ['_']
  | [], _, bs, h => by
      cases bs with
      | nil => simp [encodeBytes] at h
      | cons b bs' =>
          simp only [encodeBytes] at h
          by_cases hp : passesThrough b = true
          · rw [show encodeByte b = [Char.ofNat b.toNat] from by simp [encodeByte, hp]] at h
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
            exact absurd h.1 (pass_ne_underscore hp)
          · rw [show encodeByte b = ['_', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]
                  from by simp [encodeByte, hp]] at h
            simp at h
  | c :: p', hc, bs, h => by
      cases bs with
      | nil => simp [encodeBytes] at h
      | cons b bs' =>
          simp only [encodeBytes] at h
          by_cases hp : passesThrough b = true
          · rw [show encodeByte b = [Char.ofNat b.toNat] from by simp [encodeByte, hp]] at h
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
            exact encodeBytes_ne_snoc_underscore p'
              (fun x hx => hc x (List.mem_cons_of_mem _ hx)) bs' h.2
          · rw [show encodeByte b = ['_', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]
                  from by simp [encodeByte, hp]] at h
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
            exact absurd h.1.symm (hc c (List.mem_cons_self ..))

/-! ### The two outer layers -/

theorem no_underscore_in_keywords : ∀ k ∈ keywords, ∀ c ∈ k.toList, c ≠ '_' := by decide

theorem keywords_len : ∀ k ∈ keywords, 2 ≤ k.toList.length := by decide

theorem isKeyword_props {p : List Char} (h : isKeyword p = true) :
    (∀ c ∈ p, c ≠ '_') ∧ 2 ≤ p.length := by
  unfold isKeyword at h
  have hm : String.ofList p ∈ keywords := List.contains_iff_mem.mp h
  have h1 := no_underscore_in_keywords _ hm
  have h2 := keywords_len _ hm
  rw [String.toList_ofList] at h1 h2
  exact ⟨h1, h2⟩

/-- A prefixed core is never a keyword with `_` appended: it would have to be
    a core ending in `_`, or else start `f__` with `_` as its second
    character, and a keyword has no underscore anywhere. -/
theorem prefixedCore_ne_snoc {x : List UInt8} {p : List Char}
    (hp : ∀ c ∈ p, c ≠ '_') (hlen : 2 ≤ p.length) :
    prefixedCore (encodeBytes x) ≠ p ++ ['_'] := by
  unfold prefixedCore
  split
  · exact encodeBytes_ne_snoc_underscore p hp x
  · intro h
    match p, hlen with
    | c1 :: c2 :: p', _ =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact absurd h.2.1.symm (hp c2 (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem keywordSuffixed_inj {x y : List UInt8}
    (h : keywordSuffixed (prefixedCore (encodeBytes x))
       = keywordSuffixed (prefixedCore (encodeBytes y))) :
    prefixedCore (encodeBytes x) = prefixedCore (encodeBytes y) := by
  unfold keywordSuffixed at h
  by_cases hkx : isKeyword (prefixedCore (encodeBytes x)) = true
  · by_cases hky : isKeyword (prefixedCore (encodeBytes y)) = true
    · rw [if_pos hkx, if_pos hky] at h
      exact List.append_cancel_right h
    · rw [if_pos hkx, if_neg hky] at h
      exact absurd h.symm
        (prefixedCore_ne_snoc (isKeyword_props hkx).1 (isKeyword_props hkx).2)
  · by_cases hky : isKeyword (prefixedCore (encodeBytes y)) = true
    · rw [if_neg hkx, if_pos hky] at h
      exact absurd h
        (prefixedCore_ne_snoc (isKeyword_props hky).1 (isKeyword_props hky).2)
    · rw [if_neg hkx, if_neg hky] at h
      exact h

theorem prefixedCore_inj {x y : List UInt8}
    (h : prefixedCore (encodeBytes x) = prefixedCore (encodeBytes y)) :
    encodeBytes x = encodeBytes y := by
  unfold prefixedCore at h
  split at h <;> split at h
  · exact h
  · exact absurd h (encodeBytes_ne_f2 x _)
  · exact absurd h.symm (encodeBytes_ne_f2 y _)
  · simpa using h

/-! ### mangle -/

theorem toUTF8_data_toList_inj {a b : String}
    (h : a.toUTF8.data.toList = b.toUTF8.data.toList) : a = b :=
  String.toByteArray_inj.mp (ByteArray.ext (Array.ext' h))

theorem mangleChars_of_mangle {a b : String} (h : mangle a = mangle b) :
    mangleChars a = mangleChars b := by
  have e := congrArg String.toList h
  simpa [mangle, String.toList_ofList] using e

/-- Distinct member names give distinct identifiers: two distinct members
    never become one column, and two distinct tables never one module.

    Three layers, each injective on the image of the one below. The encoding
    is prefix-free, so its concatenation is injective; the `f__` prefix is
    unreachable by a core, so prefixed and unprefixed stay disjoint; and no
    core ends in `_`, so a keyword with `_` appended is not a prefixed core. -/
theorem mangle_injective {a b : String} (h : mangle a = mangle b) : a = b := by
  have h1 : mangleChars a = mangleChars b := mangleChars_of_mangle h
  unfold mangleChars at h1
  exact toUTF8_data_toList_inj (encodeBytes_injective (prefixedCore_inj (keywordSuffixed_inj h1)))

/-! ### Not a keyword

Does not follow from injectivity: drop the keyword rule and both
`mangle_injective` and `mangle_starts_lower` still hold, while the generator
emits `type t = { let : int }`, which OCaml rejects. -/

/-- The keyword rule fixes what it is there to fix. Either the core was not a
    keyword and is returned untouched, or it was and the `_` appended makes it
    one no longer -- no keyword contains an underscore. -/
theorem mangleChars_not_keyword (s : String) : isKeyword (mangleChars s) = false := by
  unfold mangleChars keywordSuffixed
  by_cases hk : isKeyword (prefixedCore (encodeBytes s.toUTF8.data.toList)) = true
  · rw [if_pos hk]
    cases hs : isKeyword (prefixedCore (encodeBytes s.toUTF8.data.toList) ++ ['_']) with
    | false => rfl
    | true => exact absurd rfl ((isKeyword_props hs).1 '_' (by simp))
  · rw [if_neg hk]
    simp only [Bool.not_eq_true] at hk
    exact hk

/-- With `mangle_starts_lower`, this is what "legal identifier" amounts to for
    the fragment of OCaml the generator emits. -/
theorem mangle_not_keyword (s : String) : mangle s ∉ keywords := by
  intro h
  have hc : isKeyword (mangleChars s) = true := List.contains_iff_mem.mpr h
  rw [mangleChars_not_keyword s] at hc
  exact Bool.false_ne_true hc

/-! ### The first character -/

theorem startsLower_cons {p : List Char} (h : startsLower p = true) :
    ∃ c t, p = c :: t ∧ 'a' ≤ c ∧ c ≤ 'z' := by
  cases p with
  | nil => simp [startsLower] at h
  | cons c t =>
      simp only [startsLower, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨c, t, rfl, h.1, h.2⟩

theorem prefixedCore_starts_lower (core : List Char) :
    ∃ c t, prefixedCore core = c :: t ∧ 'a' ≤ c ∧ c ≤ 'z' := by
  unfold prefixedCore
  split
  · next h => exact startsLower_cons h
  · exact ⟨'f', '_' :: '_' :: core, rfl, by decide, by decide⟩

/-- A mangled name always begins with a lowercase letter, which is what makes
    capitalising one character injective, and so module names distinct.

    Nothing about the core is needed: whichever branch the prefix rule takes
    the first character is lowercase, and the keyword rule only appends. -/
theorem mangle_starts_lower (s : String) :
    ∃ c t, mangle s = String.ofList (c :: t) ∧ 'a' ≤ c ∧ c ≤ 'z' := by
  obtain ⟨c, t, ht, h1, h2⟩ := prefixedCore_starts_lower (encodeBytes s.toUTF8.data.toList)
  refine ⟨c, ?_, ?_, h1, h2⟩
  case refine_1 => exact if isKeyword (prefixedCore (encodeBytes s.toUTF8.data.toList))
                        then t ++ ['_'] else t
  unfold mangle mangleChars keywordSuffixed
  split <;> rw [ht] <;> simp

end Tatami
