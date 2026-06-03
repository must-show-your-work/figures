/-
Figures/Vec2.lean — `Pos2` vector arithmetic.

Adds add/sub/scale/dot/norm/normalize/lerp + `HAdd`/`HSub`/`HMul`
instances so position math reads like math rather than tuple noise.
The force-directed solver lives downstream of this; both Lowering's
post-passes and the solver lean on these.

`Pos2` itself stays as `Float × Float` (defined in `Figures.lean`);
this file only adds the namespace functions and operator instances.
-/

import Figures

namespace Figures.Pos2

@[inline] def add (p q : Pos2) : Pos2 := (p.x + q.x, p.y + q.y)
@[inline] def sub (p q : Pos2) : Pos2 := (p.x - q.x, p.y - q.y)
@[inline] def neg (p : Pos2)   : Pos2 := (-p.x, -p.y)
@[inline] def smul (s : Float) (p : Pos2) : Pos2 := (s * p.x, s * p.y)
@[inline] def dot (p q : Pos2) : Float := p.x * q.x + p.y * q.y
@[inline] def normSq (p : Pos2) : Float := dot p p
@[inline] def norm (p : Pos2) : Float := (normSq p).sqrt
@[inline] def distance (p q : Pos2) : Float := norm (sub p q)

/-- Unit-vector in the direction of `p`, or `(0, 0)` if `p` is the
zero vector. -/
@[inline] def normalize (p : Pos2) : Pos2 :=
  let n := norm p
  if n < 1e-12 then (0, 0) else smul (1 / n) p

/-- Linear interpolation: `lerp a b t` is `a` at `t = 0`, `b` at
`t = 1`. -/
@[inline] def lerp (a b : Pos2) (t : Float) : Pos2 :=
  add a (smul t (sub b a))

instance : HAdd Pos2 Pos2 Pos2 := ⟨add⟩
instance : HSub Pos2 Pos2 Pos2 := ⟨sub⟩
instance : Neg Pos2            := ⟨neg⟩
instance : HMul Float Pos2 Pos2 := ⟨smul⟩

end Figures.Pos2
