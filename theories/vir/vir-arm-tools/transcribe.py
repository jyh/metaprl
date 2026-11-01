#!/usr/bin/env python3
r"""
transcribe.py VIR_REPO OUT.ml  --  the A.2 transcription check (O95, B').

Reads each VIR definition AS THE FROZEN OBJECT AND THE SHARED INPUTS WRITE IT
(I2's four specs and I3's U from inputs/router-inputs.md; J2's two specs, J3's U2
and J4's F2 from inputs/program2-inputs.md; A.3's fused term F from
object/appendix-A.tex), translates A.2's surface syntax to MetaPRL term text, and
writes a theory in which each definition gets one rule

    interactive_rw tc_<name> : <translated text> <--> <the hand-written term>

MetaPRL is the comparator: each rule is proved by unfolding <name> alone
(steps/tc.mp), so it closes iff the hand-written definition is alpha-equal to the
object's text under the mapping below. A rule left open is a FINDING.

The mapping (the whole "grammar"), declared:
  forms   guard->vguard  return->vreturn  drop->vdrop  (advance, read_u32,
          let_lin, let_atom, take and the spec names unchanged)
  calls   len(x)->vlen{x}; has_tokens/can_access/dec_tokens(a, b)->op{a; b}
  consts  MAGIC->vir_magic  ERR_X->err_x  true/false->btrue/bfalse
  infix   a >= b -> ge_bool{a; b}   a <= b -> le_bool{a; b}   a = b -> beq_int{a; b}
          a /\ b -> band{a; b} (right-assoc)   a + b -> a +@ b   a - b -> a -@ b
  tuple   (a, b) -> pair{a; b}
  vars    every variable reference is 'v; binders are bare; a prime becomes _p;
          the parameter bucket_st is the hand-written terms' st (I4: "bucket_st'
          for st'"), declared, not hidden.
LIMIT: it checks the definitions' BODIES; a definition's left-hand side (its
parameter list) is written once by hand in HEADS below.
"""
import re, sys

TEXSUB = [(r"`\\uc\{\$_\{(\d)\}\$\}`", r"\1"), (r"`\\uc\{\$\\ge\$\}`", "≥"),
          (r"`\\uc\{\$\\wedge\$\}`", "∧"), (r"`\\uc\{\$\\le\$\}`", "≤")]

def blocks_md(path):
    out, cur, on = [], [], False
    for line in open(path, encoding="utf-8"):
        if line.startswith("```"):
            if on:
                out.append("".join(cur)); cur = []
            on = not on
            continue
        if on:
            cur.append(line)
    return out

def defs_from(text):
    """Split a code block into  name -> body  at each top-level 'NAME... ≡'."""
    text = re.sub(r"\(\*.*?\*\)", " ", text, flags=re.S)
    parts = re.split(r"(?m)^(\w+)(?:\{[^\n]*\})?\s*≡", text)
    return {parts[i]: parts[i + 1].strip() for i in range(1, len(parts), 2)}

def fused_F(tex):
    s = open(tex, encoding="utf-8").read()
    i = s.index("Synthesized & Fused Single-Pass VIR Term")
    body = s[s.index("\n", i) + 1: s.index("\\end{lstlisting}", i)]
    for a, b in TEXSUB:
        body = re.sub(a, b, body)
    return body.strip()

TOK = re.compile(r"\s*(?:(\d+|0x[0-9A-Fa-f]+)|([A-Za-z_][A-Za-z0-9_']*)|(≥|≤|∧|−|[-+=(){}\[\];.,]))")

def lex(s):
    toks, i = [], 0
    while i < len(s):
        m = TOK.match(s, i)
        if not m or m.end() == i:
            if s[i:].strip() == "":
                break
            raise SyntaxError("cannot lex at: %r" % s[i:i + 30])
        i = m.end()
        num, name, sym = m.groups()
        toks.append(("num", num) if num else ("name", name) if name else ("sym", "-" if sym == "−" else sym))
    return toks

FORMS = {"guard": "vguard", "return": "vreturn", "drop": "vdrop"}
CALLS = {"len": "vlen", "has_tokens": "has_tokens", "can_access": "can_access", "dec_tokens": "dec_tokens"}
CONST = {"MAGIC": "vir_magic", "true": "btrue", "false": "bfalse"}
RENAME = {"bucket_st": "st"}

class P:
    def __init__(self, toks): self.t, self.i = toks, 0
    def peek(self, k=0): return self.t[self.i + k] if self.i + k < len(self.t) else ("eof", None)
    def eat(self, v=None):
        tok = self.peek()
        if v is not None and tok[1] != v:
            raise SyntaxError("expected %r, got %r at token %d" % (v, tok, self.i))
        self.i += 1
        return tok

    def var(self, n):
        n = RENAME.get(n, n).replace("'", "_p")
        return n

    # e ::= NAME{args} | NAME[atoms] | NAME | atom
    def expr(self):
        k, n = self.peek()
        if k == "name" and self.peek(1)[1] == "{" and n not in CALLS:
            self.eat(); self.eat("{")
            args = [self.arg()]
            while self.peek()[1] == ";":
                self.eat(); args.append(self.arg())
            self.eat("}")
            return "%s{%s}" % (FORMS.get(n, n), "; ".join(args))
        if k == "name" and self.peek(1)[1] == "[":
            self.eat(); self.eat("[")
            xs = [self.atom()]
            while self.peek()[1] == ";":
                self.eat(); xs.append(self.atom())
            self.eat("]")
            return "'%s[%s]" % (self.var(n), "; ".join(xs))
        return self.atom()

    # arg ::= v1, ..., vn . e   |  e
    def arg(self):
        j, names = self.i, []
        while self.peek()[0] == "name":
            names.append(self.var(self.eat()[1]))
            if self.peek()[1] == ",": self.eat(); continue
            break
        if names and self.peek()[1] == ".":
            self.eat()
            return "%s. %s" % (", ".join(names), self.expr())
        self.i = j
        return self.expr()

    # atom ::= conj ; precedence  ∧ < relop < + -
    def atom(self):
        a = self.rel()
        if self.peek()[1] == "∧":
            self.eat(); return "band{%s; %s}" % (a, self.atom())
        return a
    def rel(self):
        a = self.sum()
        op = self.peek()[1]
        if op in ("≥", "≤", "="):
            self.eat(); b = self.sum()
            return {"≥": "ge_bool{%s; %s}", "≤": "le_bool{%s; %s}", "=": "beq_int{%s; %s}"}[op] % (a, b)
        return a
    def sum(self):
        a = self.prim()
        while self.peek()[1] in ("+", "-"):
            op = self.eat()[1]; b = self.prim()
            a = "(%s %s %s)" % (a, "+@" if op == "+" else "-@", b)
        return a
    def prim(self):
        k, n = self.peek()
        if k == "num":
            self.eat(); return str(int(n, 0))
        if n == "(":
            self.eat(); a = self.atom()
            if self.peek()[1] == ",":
                self.eat(); b = self.atom(); self.eat(")")
                return "pair{%s; %s}" % (a, b)
            self.eat(")"); return a
        if k == "name":
            self.eat()
            if n in CALLS and self.peek()[1] == "(":
                self.eat("("); xs = [self.atom()]
                while self.peek()[1] == ",":
                    self.eat(); xs.append(self.atom())
                self.eat(")")
                return "%s{%s}" % (CALLS[n], "; ".join(xs))
            if n in CONST: return CONST[n]
            if n.startswith("ERR_"): return n.lower()
            if self.peek()[1] in ("{", "["):
                self.i -= 1; return self.expr()
            return "'" + self.var(n)
        raise SyntaxError("unexpected %r at token %d" % ((k, n), self.i))

def translate(text):
    p = P(lex(text))
    e = p.expr()
    if p.peek()[0] != "eof":
        raise SyntaxError("trailing tokens from %d: %r" % (p.i, p.t[p.i:p.i + 5]))
    return e

# The hand-written left-hand sides (the parameter lists), from vir.ml / vir2.ml.
HEADS = {
    "parse_header": "parse_header{'b0; s, sender, topic. 'k['s; 'sender; 'topic]}",
    "check_rate_limit": "check_rate_limit{'st; 'p; st2. 'k['st2]}",
    "verify_acl": "verify_acl{'p; 't; 'k}",
    "emit_payload": "emit_payload{'s; 'st}",
    "U": "vir_U{'b0; 'st}",
    "F": "vir_F{'b0; 'st}",
    "parse_header2": "parse_header2{'b0; s, sender, topic, off, n. 'k['s; 'sender; 'topic; 'off; 'n]}",
    "emit_payload2": "emit_payload2{'s; 'off; 'n; 'st}",
    "U2": "vir_U2{'b0; 'st}",
    "F2": "vir_F2{'b0; 'st}",
}

def main():
    vir, out = sys.argv[1], sys.argv[2]
    src = {}
    for b in blocks_md(vir + "/inputs/router-inputs.md") + blocks_md(vir + "/inputs/program2-inputs.md"):
        for n, body in defs_from(b).items():
            if n in HEADS: src[n] = body
    src["F"] = fused_F(vir + "/object/appendix-A.tex")
    missing = sorted(set(HEADS) - set(src))
    if missing:
        sys.exit("transcribe: no source text for %s" % missing)
    lines = ["(*", " * O95 transcription check (generated by vir-arm-tools/transcribe.py; do not edit).",
             " * Each rule: the object's/inputs' text, translated  <-->  the hand-written term.", " *)",
             "extends Vir2", "", "open Basic_tactics", ""]
    for n in HEADS:
        lines += ["interactive_rw tc_%s :" % n, "   %s" % translate(src[n]), "   <--> %s" % HEADS[n], ""]
    open(out, "w", encoding="utf-8").write("\n".join(lines))
    print("transcribe: %d definitions -> %s" % (len(HEADS), out))

if __name__ == "__main__":
    main()
