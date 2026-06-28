/-
Figures/Labels/SimpleLatex.lean — a minimal LaTeX → SVG `<tspan>`
renderer.

Covers the subset of LaTeX that category-theory and synthetic-geometry
labels actually need:

- subscripts `_X` or `_{XYZ}`        (nested `_` allowed)
- superscripts `^X` or `^{XYZ}`      (and primes `'` → ′)
- Greek letters `\alpha` ... `\omega`, `\Alpha` ... `\Omega`
- Standard math operators (`\to`, `\circ`, `\otimes`, `\oplus`, etc.)
- `\mathrm{X}`, `\mathbf{X}`, `\mathcal{X}`, `\mathbb{X}` — emitted
  as plain text in V1; V2 swaps in stylized unicode / SVG `<g>`
  with font-family overrides.
- Plain text passes through verbatim.

What's deliberately not supported here:
- `\frac{}{}` (would need a separate SVG element with a divider line)
- `\sum_{i=1}^{n}` with limits above / below (positioning math)
- Anything matrix-shaped
- Anything that requires actual LaTeX layout math (TeX boxes, stretchy
  delimiters, etc.)

Those should go through the heavy backend (tectonic + dvisvgm) when
it lands. For category-theory diagrams the simple subset is what
99% of labels need — subscript-superscript + Greek + identifiers.
-/

namespace Figures.Labels.SimpleLatex


/-! ## Token AST -/

mutual
inductive Token where
  | plain    (text : String)               : Token
  | greek    (name : String)               : Token
  | symbol   (name : String)               : Token
  | subscr   (body : Group)                : Token
  | super    (body : Group)                : Token
  | styled   (style : StyleTag) (body : Group) : Token
deriving Repr, Inhabited

inductive Group where
  | one (t : Token)          : Group
  | many (ts : Array Token)  : Group
deriving Repr, Inhabited

inductive StyleTag where
  | mathrm
  | mathbf
  | mathcal
  | mathbb
  | mathfrak
  | mathit
deriving Repr, Inhabited
end


/-! ## Greek + symbol tables

Lowercase Greek covers the math we'll see; uppercase variants where
the upright glyph exists (typical TeX convention is upright uppercase
Greek). Symbols cover the common math operators / arrows / quantifiers
seen in category and synthetic-geometry labels. -/

def greekTable : List (String × String) := [
  ("alpha", "α"), ("beta", "β"), ("gamma", "γ"), ("delta", "δ"),
  ("epsilon", "ε"), ("varepsilon", "ε"), ("zeta", "ζ"), ("eta", "η"),
  ("theta", "θ"), ("vartheta", "ϑ"), ("iota", "ι"), ("kappa", "κ"),
  ("lambda", "λ"), ("mu", "μ"), ("nu", "ν"), ("xi", "ξ"),
  ("omicron", "ο"), ("pi", "π"), ("varpi", "ϖ"), ("rho", "ρ"),
  ("varrho", "ϱ"), ("sigma", "σ"), ("varsigma", "ς"), ("tau", "τ"),
  ("upsilon", "υ"), ("phi", "φ"), ("varphi", "ϕ"), ("chi", "χ"),
  ("psi", "ψ"), ("omega", "ω"),
  ("Alpha", "Α"), ("Beta", "Β"), ("Gamma", "Γ"), ("Delta", "Δ"),
  ("Epsilon", "Ε"), ("Zeta", "Ζ"), ("Eta", "Η"), ("Theta", "Θ"),
  ("Iota", "Ι"), ("Kappa", "Κ"), ("Lambda", "Λ"), ("Mu", "Μ"),
  ("Nu", "Ν"), ("Xi", "Ξ"), ("Omicron", "Ο"), ("Pi", "Π"),
  ("Rho", "Ρ"), ("Sigma", "Σ"), ("Tau", "Τ"), ("Upsilon", "Υ"),
  ("Phi", "Φ"), ("Chi", "Χ"), ("Psi", "Ψ"), ("Omega", "Ω")
]

def symbolTable : List (String × String) := [
  -- Arrows
  ("to", "→"), ("rightarrow", "→"), ("leftarrow", "←"),
  ("Rightarrow", "⇒"), ("Leftarrow", "⇐"), ("leftrightarrow", "↔"),
  ("Leftrightarrow", "⇔"), ("mapsto", "↦"), ("hookrightarrow", "↪"),
  ("twoheadrightarrow", "↠"), ("Longrightarrow", "⟹"),
  -- Category-theory composition
  ("circ", "∘"), ("bullet", "•"), ("cdot", "·"),
  -- Operators
  ("otimes", "⊗"), ("oplus", "⊕"), ("times", "×"), ("pm", "±"),
  ("mp", "∓"), ("cup", "∪"), ("cap", "∩"),
  -- Relations
  ("leq", "≤"), ("geq", "≥"), ("neq", "≠"), ("approx", "≈"),
  ("equiv", "≡"), ("cong", "≅"), ("sim", "∼"),
  ("subset", "⊂"), ("subseteq", "⊆"), ("supset", "⊃"), ("supseteq", "⊇"),
  ("in", "∈"), ("notin", "∉"), ("ni", "∋"),
  -- Quantifiers / logic
  ("forall", "∀"), ("exists", "∃"), ("neg", "¬"), ("land", "∧"),
  ("lor", "∨"), ("Rightarrow", "⇒"),
  -- Misc
  ("infty", "∞"), ("partial", "∂"), ("nabla", "∇"), ("emptyset", "∅"),
  ("star", "⋆"), ("ast", "∗"), ("dagger", "†"),
  -- Common category markers
  ("op", "op")  -- treated as plain text since `^{op}` is the use case
]


/-! ## Parser

Streaming over String position. We keep it manual rather than reaching
for a parser combinator — the grammar is small, performance matters
on every label render. -/

private structure ParseState where
  source : String
  pos    : String.Pos.Raw := 0
deriving Inhabited

private def ParseState.atEnd (s : ParseState) : Bool := s.source.atEnd s.pos
private def ParseState.peek (s : ParseState) : Char := s.source.get s.pos
private def ParseState.advance (s : ParseState) : ParseState :=
  { s with pos := s.source.next s.pos }
private def ParseState.consumeChar (s : ParseState) : Char × ParseState :=
  (s.peek, s.advance)

/-- Consume a sequence of characters while `cond` holds, returning the
collected string and the advanced state. -/
private partial def takeWhile (s : ParseState) (cond : Char → Bool) :
    String × ParseState :=
  if s.atEnd then ("", s)
  else if cond s.peek then
    let (acc, s') := takeWhile s.advance cond
    (s.peek.toString ++ acc, s')
  else
    ("", s)

private def isPlainChar (c : Char) : Bool :=
  c ≠ '_' ∧ c ≠ '^' ∧ c ≠ '\\' ∧ c ≠ '{' ∧ c ≠ '}' ∧ c ≠ '\''

private def isCommandChar (c : Char) : Bool := c.isAlpha

private def lookupStyle (name : String) : Option StyleTag :=
  match name with
  | "mathrm"   => some .mathrm
  | "mathbf"   => some .mathbf
  | "mathcal"  => some .mathcal
  | "mathbb"   => some .mathbb
  | "mathfrak" => some .mathfrak
  | "mathit"   => some .mathit
  | _          => none

/-- Skip ASCII space characters. Used between style commands and their
group argument since LaTeX is whitespace-permissive there. -/
private partial def skipSpaces (s : ParseState) : ParseState :=
  if s.atEnd then s
  else if s.peek == ' ' then skipSpaces s.advance
  else s

mutual
/-- Parse a single atomic token starting at the current position. -/
private partial def parseAtom (s : ParseState) : Option (Token × ParseState) :=
  if s.atEnd then none
  else
    let c := s.peek
    if c == '\\' then
      parseCommand s.advance
    else if c == '_' then
      let s' := s.advance
      match parseGroupOrSingle s' with
      | some (g, s'') => some (Token.subscr g, s'')
      | none          => none
    else if c == '^' then
      let s' := s.advance
      match parseGroupOrSingle s' with
      | some (g, s'') => some (Token.super g, s'')
      | none          => none
    else if c == '\'' then
      -- Prime: render as superscript ′ (Unicode PRIME U+2032).
      some (Token.super (.one (.plain "′")), s.advance)
    else if isPlainChar c then
      let (text, s') := takeWhile s isPlainChar
      some (Token.plain text, s')
    else
      -- Stray `{` or `}` outside a group context — skip it.
      some (Token.plain c.toString, s.advance)

/-- Parse a `\commandName` (already past the `\`). -/
private partial def parseCommand (s : ParseState) :
    Option (Token × ParseState) :=
  let (name, s') := takeWhile s isCommandChar
  if name.isEmpty then
    -- Lone backslash; treat as plain.
    some (Token.plain "\\", s)
  else
    match lookupStyle name with
    | some style =>
      -- Style commands take a single group argument.
      let s'' := skipSpaces s'
      if s''.atEnd || s''.peek ≠ '{' then
        -- No argument; treat the command name as plain text.
        some (Token.plain name, s')
      else
        match parseGroupOrSingle s'' with
        | some (g, s''') => some (Token.styled style g, s''')
        | none           => some (Token.plain name, s')
    | none =>
      match greekTable.find? (·.1 == name) with
      | some (_, glyph) => some (Token.greek glyph, s')
      | none =>
        match symbolTable.find? (·.1 == name) with
        | some (_, glyph) => some (Token.symbol glyph, s')
        | none            =>
          -- Unknown command — emit the name verbatim so we at least
          -- see something, instead of silently dropping it.
          some (Token.plain s!"\\{name}", s')

/-- Parse either a `{ … }` group or a single atom (for `_X` / `^X`
without braces). -/
private partial def parseGroupOrSingle (s : ParseState) :
    Option (Group × ParseState) :=
  if s.atEnd then none
  else if s.peek == '{' then
    parseGroup s.advance
  else
    match parseAtom s with
    | some (t, s') => some (Group.one t, s')
    | none         => none

/-- Parse tokens until a closing `}` (assumes we just consumed `{`). -/
private partial def parseGroup (s : ParseState) :
    Option (Group × ParseState) :=
  let rec loop (acc : Array Token) (s : ParseState) :
      Option (Array Token × ParseState) :=
    if s.atEnd then
      -- Unterminated group: return what we have.
      some (acc, s)
    else if s.peek == '}' then
      some (acc, s.advance)
    else
      match parseAtom s with
      | some (t, s') => loop (acc.push t) s'
      | none         => some (acc, s)
  let (toks, s') := (loop #[] s).getD (#[], s)
  some (Group.many toks, s')

end

/-- Parse a complete LaTeX label source into a token list. -/
partial def parse (source : String) : Array Token := Id.run do
  let mut s : ParseState := { source := source }
  let mut acc : Array Token := #[]
  while !s.atEnd do
    match parseAtom s with
    | some (t, s') => acc := acc.push t; s := s'
    | none         => break
  acc


/-! ## SVG rendering

Tokens render to `<tspan>` children of a parent `<text>` element.
Subscripts and superscripts use SVG's `baseline-shift` + reduced
`font-size`. We also nudge a hair smaller for nested levels — that's
where SVG falls short (no native nested-script support); the renderer
tracks depth and shrinks proportionally. -/

private def escapeXml (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"

private def styleAttrs (style : StyleTag) : String :=
  match style with
  | .mathrm   => " font-style=\"normal\""
  | .mathbf   => " font-weight=\"bold\""
  | .mathit   => " font-style=\"italic\""
  -- mathcal / mathbb / mathfrak would need stylized font-families;
  -- for V1 fall back to italic + slightly smaller (mathbb / mathfrak
  -- glyphs aren't widely available without OpenType math fonts).
  | .mathcal  => " font-style=\"italic\""
  | .mathbb   => " font-style=\"italic\""
  | .mathfrak => " font-style=\"italic\""

mutual
private partial def renderToken (depth : Nat) (t : Token) : String :=
  match t with
  | .plain text => s!"<tspan>{escapeXml text}</tspan>"
  | .greek glyph => s!"<tspan>{escapeXml glyph}</tspan>"
  | .symbol glyph => s!"<tspan>{escapeXml glyph}</tspan>"
  | .subscr body =>
    let inner := renderGroup (depth + 1) body
    -- 70% of parent size per level, baseline shifted down.
    let sz := (70 : Nat).max (70 - depth * 5)
    s!"<tspan baseline-shift=\"sub\" font-size=\"{sz}%\">{inner}</tspan>"
  | .super body =>
    let inner := renderGroup (depth + 1) body
    let sz := (70 : Nat).max (70 - depth * 5)
    s!"<tspan baseline-shift=\"super\" font-size=\"{sz}%\">{inner}</tspan>"
  | .styled style body =>
    let inner := renderGroup depth body
    s!"<tspan{styleAttrs style}>{inner}</tspan>"

private partial def renderGroup (depth : Nat) (g : Group) : String :=
  match g with
  | .one t => renderToken depth t
  | .many ts => String.intercalate "" (ts.toList.map (renderToken depth))
end

/-- Render a parsed token list as the inner content of an SVG `<text>`
element. The caller wraps with `<text x= y= …>…</text>`. -/
def renderTokens (tokens : Array Token) : String :=
  String.intercalate "" (tokens.toList.map (renderToken 0))

/-- One-shot: parse a LaTeX source string and produce the SVG inner
content. Equivalent to `renderTokens (parse source)`. -/
def render (source : String) : String :=
  renderTokens (parse source)

end Figures.Labels.SimpleLatex
