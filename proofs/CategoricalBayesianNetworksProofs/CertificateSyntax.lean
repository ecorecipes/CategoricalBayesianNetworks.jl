import Lean.Data.Json.Parser

/-!
# Strict JSON syntax for finite certificates

This parser accepts the JSON fragment used by `OpenNet.RawCertificate/v1`.
Numbers must be integer tokens: fractions and exponent notation are rejected,
not rounded. Decoded duplicate object keys, trailing input, invalid escapes and
unpaired UTF-16 surrogates are rejected. Strings preserve valid Unicode.

Recursion is explicitly fuelled by the input character count, rather than a
project-specific partial or native proof implementation. Standard Lean JSON
lexical primitives are used for integer digits and hexadecimal escapes.
-/

namespace OpenNet.CertificateSyntax
open Lean
open Std.Internal.Parsec Std.Internal.Parsec.String

def escaped : Parser Char := do
  match ← any with
  | '\\' => return '\\'
  | '"' => return '"'
  | '/' => return '/'
  | 'b' => return '\x08'
  | 'f' => return '\x0c'
  | 'n' => return '\n'
  | 'r' => return '\x0d'
  | 't' => return '\t'
  | 'u' =>
    let a ← Json.Parser.hexChar
    let b ← Json.Parser.hexChar
    let c ← Json.Parser.hexChar
    let d ← Json.Parser.hexChar
    let value := (a <<< 12) ||| (b <<< 8) ||| (c <<< 4) ||| d
    if 0xD800 ≤ value && value < 0xDC00 then
      Json.Parser.finishSurrogatePair value
    else if 0xDC00 ≤ value && value < 0xE000 then
      fail "unpaired Unicode surrogate"
    else if h : value.toUInt32.isValidChar then
      return ⟨value.toUInt32, h⟩
    else
      fail "invalid Unicode code point"
  | _ => fail "invalid string escape"

def stringBody : Nat → String → Parser String
  | 0, _ => fail "JSON nesting/string budget exhausted"
  | fuel + 1, acc => do
    let c ← any
    if c == '"' then
      return acc
    else if c == '\\' then
      stringBody fuel (acc.push (← escaped))
    else if c.val < 0x20 then
      fail "unescaped control character in string"
    else
      stringBody fuel (acc.push c)

def integer : Parser JsonNumber := do
  let sign ← Json.Parser.numSign
  let n ← Json.Parser.nat
  if !(← isEof) then
    let c ← peek!
    if c == '.' || c == 'e' || c == 'E' then
      fail "certificate numbers must be integer tokens (no decimal or exponent notation)"
  return JsonNumber.fromInt (sign * n)

mutual
  def value : Nat → Parser Json
    | 0 => fail "JSON nesting budget exhausted"
    | fuel + 1 => do
      let c ← peek!
      if c == '{' then
        skip; ws
        if (← peek!) == '}' then
          skip; ws
          return Json.obj ∅
        else
          let obj ← object fuel ∅
          return Json.obj obj
      else if c == '[' then
        skip; ws
        if (← peek!) == ']' then
          skip; ws
          return Json.arr #[]
        else
          let arr ← array fuel #[]
          return Json.arr arr
      else if c == '"' then
        skip
        let s ← stringBody fuel ""
        ws
        return Json.str s
      else if c == 't' then
        skipString "true"; ws
        return Json.bool true
      else if c == 'f' then
        skipString "false"; ws
        return Json.bool false
      else if c == 'n' then
        skipString "null"; ws
        return Json.null
      else if c == '-' || ('0' ≤ c && c ≤ '9') then
        let n ← integer
        ws
        return Json.num n
      else
        fail "unexpected JSON input"

  def array : Nat → Array Json → Parser (Array Json)
    | 0, _ => fail "JSON array budget exhausted"
    | fuel + 1, acc => do
      let element ← value fuel
      let acc := acc.push element
      let c ← any
      if c == ']' then
        ws
        return acc
      else if c == ',' then
        ws
        array fuel acc
      else
        fail "expected ',' or ']'"

  def object : Nat → Std.TreeMap.Raw String Json → Parser (Std.TreeMap.Raw String Json)
    | 0, _ => fail "JSON object budget exhausted"
    | fuel + 1, acc => do
      if (← any) != '"' then fail "expected object key"
      let key ← stringBody fuel ""
      if acc.contains key then fail s!"duplicate object key: {key}"
      ws
      if (← any) != ':' then fail "expected ':'"
      ws
      let element ← value fuel
      let acc := acc.insert key element
      let c ← any
      if c == '}' then
        ws
        return acc
      else if c == ',' then
        ws
        object fuel acc
      else
        fail "expected ',' or '}'"
end

def parse (text : String) : Except String Json :=
  Parser.run (do
    ws
    let result ← value (text.length + 1)
    eof
    return result) text

end OpenNet.CertificateSyntax
