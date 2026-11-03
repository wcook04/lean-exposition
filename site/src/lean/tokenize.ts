// A Lean 4 tokenizer for reading, with no dependencies. It colours source and finds
// the names a reader can open; it does not parse. Concatenating the token texts always
// returns the input. A module of 2,000 lines tokenizes in a few milliseconds.

export type LeanTokenKind =
  | "space"
  | "comment"
  | "doc"
  | "string"
  | "attr"
  | "keyword"
  | "tactic"
  | "binder"
  | "number"
  | "op"
  | "bracket"
  | "type"
  | "name";

export interface LeanToken {
  kind: LeanTokenKind;
  text: string;
  /** For a binder written `(x : T ...)`: the first name of `T`. */
  of?: string;
}

const KEYWORDS = new Set(
  (
    "theorem lemma def abbrev structure class instance inductive example axiom opaque namespace section end open " +
    "variable universe import noncomputable private protected partial unsafe extends where with deriving export " +
    "fun λ let in if then else match do Type Prop Sort mutual macro syntax notation infix infixl infixr prefix postfix " +
    "local scoped attribute set_option omit include using at from"
  ).split(" "),
);

/** Words that are always tactics or proof structure in this source. */
const TACTICS = new Set(
  (
    "by have show suffices calc obtain rcases rintro intro intros apply exact refine refine' simp simpa simp_all simp_rw dsimp " +
    "rw rwa erw nth_rewrite nth_rw filter_upwards linarith nlinarith norm_num norm_cast push_cast positivity gcongr " +
    "field_simp ring_nf linear_combination omega decide aesop tauto contradiction exfalso by_contra by_cases rfl " +
    "all_goals any_goals try repeat first constructor unfold change convert convert_to specialize rename_i lift " +
    "fun_prop measurability continuity exact_mod_cast assumption trivial nofun nomatch infer_instance " +
    "classical funext congrm subst symm trans induction induction' cases cases' rcases' interval_integrable " +
    "bound_tac peel choose wlog next swap pick_goal absurd"
  ).split(" "),
);

/** Tactics whose words are also ordinary names: only where a tactic can start. */
const POSITIONAL_TACTICS = new Set("left right use ext ring field congr bound set let_fun rel abel nth_rw exacts".split(" "));
const TACTIC_LEAD = new Set(["by", "·", ";", "<;>", "(", "|", "then", "else", "=>", "try", "repeat", "all_goals", "any_goals", "first"]);

const QUANTIFIERS = new Set(["∀", "∃", "∃!", "fun", "λ", "∀ᵐ", "∃ᵐ", "∀ᶠ", "∃ᶠ", "∫", "∑", "∏", "⨆", "⨅"]);
const NAMED_BY_NEXT = new Set(["have", "let", "set", "suffices", "obtain"]);
const NAMES_TO_LINE_END = new Set(["intro", "intros", "rintro", "ext", "funext", "rename_i", "with"]);

const OPEN = new Set(["(", "{", "[", "⦃", "⟨"]);
const CLOSE = new Set([")", "}", "]", "⦄", "⟩"]);

const SPACE = /\s+/y;
const NUMBER = /0[xX][0-9a-fA-F]+|\d+(?:\.\d+)?(?:[eE][+-]?\d+)?/y;
const STRING = /"(?:[^"\\]|\\[\s\S])*"?/y;
const CHAR = /'(?:\\.|[^'\\\n])'/uy;
const ATTR = /@\[[^\]\n]*\]/y;
const COMMAND = /#[a-z_]+/y;
const OPERATOR = /:=|=>|->|<->|<-|<;>|<\|>|\|>\.?|<\||\.\.\.?|=ᵐ|≤ᵐ|=ᶠ|≤ᶠ|∀ᵐ|∃ᵐ|∀ᶠ|∃ᶠ|∃!|⁻¹/y;
const SEGMENT = "(?:«[^»\\n]*»|[\\p{L}_][\\p{L}\\p{N}\\p{M}_'!?]*)";
const IDENT = new RegExp(`\\.?${SEGMENT}(?:\\.(?:«[^»\\n]*»|[\\p{L}\\p{N}_][\\p{L}\\p{N}\\p{M}_'!?]*))*`, "uy");
const UPPER = /^[\p{Lu}]/u;

function match(re: RegExp, source: string, at: number): string | null {
  re.lastIndex = at;
  const found = re.exec(source);
  return found ? found[0] : null;
}

/** The index just past a nested block comment that opens at `at`. */
function blockEnd(source: string, at: number): number {
  let depth = 0;
  let i = at;
  while (i < source.length) {
    if (source.startsWith("/-", i)) {
      depth++;
      i += 2;
    } else if (source.startsWith("-/", i)) {
      depth--;
      i += 2;
      if (depth === 0) return i;
    } else i++;
  }
  return source.length;
}

function nameKind(text: string): LeanTokenKind {
  const last = text.slice(text.lastIndexOf(".") + 1);
  return UPPER.test(last) ? "type" : "name";
}

export interface TokenizeOptions {
  /** The source begins at a declaration, so its leading brackets are binders. Off for a proof on its own. */
  signature?: boolean;
}

export function tokenize(source: string, options: TokenizeOptions = {}): LeanToken[] {
  const tokens: LeanToken[] = [];
  let i = 0;
  let lineStart = true;
  let prev: LeanToken | null = null;
  const emit = (kind: LeanTokenKind, text: string) => {
    const token: LeanToken = { kind, text };
    tokens.push(token);
    i += text.length;
    if (kind !== "comment" && kind !== "doc") {
      prev = token;
      lineStart = false;
    }
  };

  while (i < source.length) {
    const c = source[i];
    const space = match(SPACE, source, i);
    if (space) {
      tokens.push({ kind: "space", text: space });
      i += space.length;
      if (space.includes("\n")) lineStart = true;
      continue;
    }
    if (source.startsWith("/-", i)) {
      emit(source.startsWith("/--", i) || source.startsWith("/-!", i) ? "doc" : "comment", source.slice(i, blockEnd(source, i)));
      continue;
    }
    if (source.startsWith("--", i)) {
      const end = source.indexOf("\n", i);
      emit("comment", source.slice(i, end < 0 ? source.length : end));
      continue;
    }
    if (c === '"') {
      emit("string", match(STRING, source, i) as string);
      continue;
    }
    if (c === "'") {
      const char = match(CHAR, source, i);
      if (char) {
        emit("string", char);
        continue;
      }
    }
    if (c === "@") {
      const attr = match(ATTR, source, i);
      if (attr) {
        emit("attr", attr);
        continue;
      }
    }
    if (c === "#") {
      const command = match(COMMAND, source, i);
      if (command) {
        emit("keyword", command);
        continue;
      }
    }
    if (OPEN.has(c) || CLOSE.has(c)) {
      emit("bracket", c);
      continue;
    }
    const op = match(OPERATOR, source, i);
    if (op) {
      emit(QUANTIFIERS.has(op) ? "keyword" : "op", op);
      continue;
    }
    if (c >= "0" && c <= "9") {
      emit("number", match(NUMBER, source, i) as string);
      continue;
    }
    const ident = match(IDENT, source, i);
    if (ident) {
      const previous = prev as LeanToken | null;
      const after = source.slice(i + ident.length).match(/^[^\S\n]*(:(?!=))?/);
      const isField = Boolean(after?.[1]);
      if (KEYWORDS.has(ident)) {
        const tacticWord = (ident === "at" || ident === "using" || ident === "from") && !previous;
        emit(tacticWord ? "name" : "keyword", ident);
      } else if (TACTICS.has(ident) && !isField) emit("tactic", ident);
      else if (ident === "only" && previous?.kind === "tactic") emit("keyword", ident);
      else if (POSITIONAL_TACTICS.has(ident) && !isField && (lineStart || (previous !== null && TACTIC_LEAD.has(previous.text)))) emit("tactic", ident);
      else emit(nameKind(ident), ident);
      continue;
    }
    const codePoint = String.fromCodePoint(source.codePointAt(i) as number);
    emit(QUANTIFIERS.has(codePoint) ? "keyword" : "op", codePoint);
  }
  markBinders(tokens, options.signature !== false);
  return tokens;
}

const isName = (t: LeanToken | undefined) => t !== undefined && (t.kind === "name" || t.kind === "type");

/** Mark the names inside `(a b : T)`, returning the index just past the group's close. */
function binderGroup(real: LeanToken[], open: number): number {
  let j = open + 1;
  const names: LeanToken[] = [];
  while (isName(real[j]) || real[j]?.text === "_") {
    if (isName(real[j])) names.push(real[j]);
    j++;
  }
  if (names.length && real[j]?.text === ":") {
    const type = isName(real[j + 1]) ? real[j + 1].text : undefined;
    for (const name of names) {
      name.kind = "binder";
      if (type) name.of = type;
    }
  }
  return closeOf(real, open) + 1;
}

function closeOf(real: LeanToken[], open: number): number {
  let depth = 0;
  for (let j = open; j < real.length; j++) {
    const t = real[j];
    if (t.kind !== "bracket") continue;
    if (OPEN.has(t.text)) depth++;
    else if (--depth === 0) return j;
  }
  return real.length - 1;
}

/** Mark every name inside an anonymous pattern such as `⟨x, hx⟩`. */
function markPattern(real: LeanToken[], open: number): number {
  const close = closeOf(real, open);
  for (let j = open + 1; j < close; j++) if (isName(real[j])) real[j].kind = "binder";
  return close + 1;
}

function markBinders(tokens: LeanToken[], signature: boolean): void {
  const real: LeanToken[] = [];
  const line: number[] = [];
  let n = 0;
  for (const t of tokens) {
    if (t.kind === "space") {
      for (const c of t.text) if (c === "\n") n++;
    } else if (t.kind !== "comment" && t.kind !== "doc") {
      real.push(t);
      line.push(n);
    }
  }

  if (signature) {
    let i = 0;
    while (i < real.length) {
      const t = real[i];
      if (t.text === ":=" || t.text === ":" || t.text === "where" || t.text === "by") break;
      if (t.kind === "bracket" && OPEN.has(t.text)) i = binderGroup(real, i);
      else i++;
    }
  }

  for (let i = 0; i < real.length; i++) {
    const t = real[i];
    if ((t.kind === "keyword" || t.kind === "op") && QUANTIFIERS.has(t.text)) {
      let j = i + 1;
      for (;;) {
        const u = real[j];
        if (isName(u)) {
          u.kind = "binder";
          j++;
        } else if (u?.text === "⟨") j = markPattern(real, j);
        else if (u?.kind === "bracket" && OPEN.has(u.text) && u.text !== "[") j = binderGroup(real, j);
        else if (u?.text === "_") j++;
        else break;
      }
    } else if ((t.kind === "tactic" || t.kind === "keyword") && NAMED_BY_NEXT.has(t.text)) {
      if (isName(real[i + 1])) real[i + 1].kind = "binder";
      else if (real[i + 1]?.text === "⟨") markPattern(real, i + 1);
    } else if ((t.kind === "tactic" || t.kind === "keyword") && NAMES_TO_LINE_END.has(t.text)) {
      for (let j = i + 1; j < real.length && line[j] === line[i]; j++) {
        const u = real[j];
        if (isName(u)) u.kind = "binder";
        else if (u.text === ";" || u.text === "<;>" || u.text === "=>") break;
        else if (u.kind !== "bracket" && u.text !== "," && u.text !== "|" && u.text !== "_" && u.text !== "-") break;
      }
    }
  }
}

export interface LinePiece {
  token: LeanToken;
  text: string;
  /** The token's position in the list, so a line can look up what was resolved for it. */
  index: number;
}

export interface TokenLine {
  /** Leading spaces, removed from `pieces` so the hanging indent can be set in CSS. */
  indent: number;
  pieces: LinePiece[];
}

/** Split tokens into source lines; a comment or space that spans lines is cut at each newline. */
export function tokenLines(tokens: LeanToken[]): TokenLine[] {
  const lines: TokenLine[] = [{ indent: 0, pieces: [] }];
  tokens.forEach((token, index) => {
    const parts = token.text.includes("\n") ? token.text.split("\n") : [token.text];
    parts.forEach((part, k) => {
      if (k > 0) lines.push({ indent: 0, pieces: [] });
      const current = lines[lines.length - 1];
      if (!part) return;
      if (!current.pieces.length && token.kind === "space") current.indent += part.length;
      else current.pieces.push({ token, text: part, index });
    });
  });
  return lines;
}
