open MParser
open Util

let ( let+ ) = ( >>= )
let ( let@ ) = ( |>> )

(* helpers *)
let with_pos p =
  let make ~sl ~sc ~el ~ec = Location.make "" sl el sc ec in
  let+ _, sl, sc = get_pos in
  let+ r = p in
  let@ _, el, ec = get_pos in
  (make ~sl ~sc ~el ~ec, r)


let integer =
  let+ sign = option (char '-') in
  let@ n = many1 digit in
  match sign with
  | Some sign -> sign :: n |> Base.String.of_list |> int_of_string
  | None -> Base.String.of_list n |> int_of_string


let float =
  let+ sign = option (char '-') in
  let+ n1 = many1 digit in
  let+ d = char '.' in
  let@ n2 = many1 digit in
  match sign with
  | Some sign -> (sign :: n1) @ (d :: n2) |> Base.String.of_list |> float_of_string
  | None -> n1 @ (d :: n2) |> Base.String.of_list |> float_of_string


let string_literal =
  char '"'
  >> let+ s = many_until any_char_or_nl (char '"') in
     Base.String.of_list s |> return


let char_literal =
  char '\''
  >> let+ c = any_char_or_nl <|> space in
     char '\'' >> return c


let ident case =
  let+ s = case in
  let+ r = many (letter <|> digit <|> char '_') in
  s :: r |> Base.String.of_list |> return


let arrow : (string, unit) t = string "->"
let fat_arrow : (string, unit) t = string "=>"
let parens p : ('a, unit) t = between (char '(') (char ')') p

(* main parsers *)
let const : (Ast.located_const, unit) t =
  let boolean = string "true" >> return true <|> (string "false" >> return false) in
  with_pos
    (let+ n = integer in
     return @@ Ast.Int n)
  <|> with_pos
        (let+ f = float in
         return @@ Ast.Float f)
  <|> with_pos
        (let+ s = string_literal in
         return @@ Ast.String s)
  <|> with_pos
        (let+ c = char_literal in
         return @@ Ast.Char c)
  <|> with_pos
        (let+ b = boolean in
         return @@ Ast.Bool b)
  <|> with_pos
        (char '@'
        >> let+ i = ident lowercase in
           return @@ Ast.Atom (Ast.Str i))
  <|> with_pos
        (let+ i = ident lowercase in
         return @@ Ast.Ident (Ast.Str i))
  <|> with_pos
        (let+ i = ident uppercase in
         return @@ Ast.Udc (Ast.Str i))


let prim : (Ast.prim, unit) t =
  let universe =
    let nat =
      let+ i = integer in
      if i >= 0 then return i
      else message (Printf.sprintf "Expected a natural number, but got %d." i)
    in
    string "Type" >> nat <|> return 0
  in
  string "Int" >> return Ast.PInt
  <|> (string "Float" >> return Ast.PFloat)
  <|> (string "String" >> return Ast.PString)
  <|> (string "Char" >> return Ast.PChar)
  <|> (string "Bool" >> return Ast.PBool)
  <|> (string "Atom" >> return Ast.PAtom)
  <|> (string "()" >> return Ast.PUnit)
  <|> let+ i = universe in
      return @@ Ast.PUni i


(* pattern parsing *)
let pattern_infix cons = Infix (string "::" >> return cons, Assoc_right)

let pattern_operator : (Ast.located_pattern, unit) operator list list =
  let combine (l, _) (r, _) = Location.combine l r in
  [ [ pattern_infix (fun l r -> (combine l r, Ast.PCons (l, r))) ] ]


let pattern_list func =
  char '[' >> optional space
  >>
  let+ ps = sep_by func (char ';') in
  optional space >> char ']' >> return (Ast.PList ps)


let pattern_ctor func =
  let+ i = ident uppercase in
  space
  >>
  let@ ps = sep_by1 func space in
  Ast.PCtor (Ast.Str i, ps)


let rec pnud s =
  let open Ast in
  (with_pos
     (let@ c = const in
      PConst c)
  <|> with_pos (char '_' >> return PWild)
  <|> with_pos (pattern_list pattern)
  <|> with_pos (pattern_ctor pattern)
  <|> parens pattern)
    s


and pattern s = expression pattern_operator pnud s

(* expression parsing *)
let expr_infix ?(assoc = Assoc_left) op cons =
  Infix (optional (many space) >> string op >> optional space >> return cons, assoc)


let expr_prefix op cons = Prefix (string op >> cons)

let operators : (Ast.located_expr, unit) operator list list =
  let combine (l, _) (r, _) = Location.combine l r in
  [
    [ expr_infix "::" (fun l r -> (combine l r, Ast.Bop (l, Ast.Cons, r))) ~assoc:Assoc_right ];
    [
      expr_infix "*" (fun l r -> (combine l r, Ast.Bop (l, Ast.IMul, r)));
      expr_infix "*." (fun l r -> (combine l r, Ast.Bop (l, Ast.FMul, r)));
      expr_infix "/" (fun l r -> (combine l r, Ast.Bop (l, Ast.IDiv, r)));
      expr_infix "/." (fun l r -> (combine l r, Ast.Bop (l, Ast.FDiv, r)));
    ];
    [
      expr_infix "+" (fun l r -> (combine l r, Ast.Bop (l, Ast.IAdd, r)));
      expr_infix "+." (fun l r -> (combine l r, Ast.Bop (l, Ast.FAdd, r)));
      expr_infix "-" (fun l r -> (combine l r, Ast.Bop (l, Ast.ISub, r)));
      expr_infix "-." (fun l r -> (combine l r, Ast.Bop (l, Ast.FSub, r)));
    ];
    [
      expr_infix "<" (fun l r -> (combine l r, Ast.Bop (l, Ast.Less, r)));
      expr_infix "<=" (fun l r -> (combine l r, Ast.Bop (l, Ast.LessE, r)));
      expr_infix ">" (fun l r -> (combine l r, Ast.Bop (l, Ast.Greater, r)));
      expr_infix ">=" (fun l r -> (combine l r, Ast.Bop (l, Ast.GreaterE, r)));
    ];
    [
      expr_infix "&&" (fun l r -> (combine l r, Ast.Bop (l, Ast.And, r)));
      expr_infix "||" (fun l r -> (combine l r, Ast.Bop (l, Ast.Or, r)));
    ];
    [
      expr_infix "/=" (fun l r -> (combine l r, Ast.Bop (l, Ast.NotEq, r)));
      expr_infix "=" (fun l r -> (combine l r, Ast.Bop (l, Ast.Equal, r)));
    ];
    [ expr_infix "->" (fun l r -> (combine l r, Ast.Pi (l, r))) ~assoc:Assoc_right ];
  ]


let list_expr func =
  char '[' >> optional space
  >>
  let+ e = sep_by func (char ';') in
  optional space >> char ']' >> return (Ast.List e)


let let_expr func =
  let ty =
    char ':' >> optional space
    >> (let+ t = func in
        optional space >> char '=' >> return (Some t))
    <|> (char '=' >> return None)
  in
  string "let" >> space
  >>
  let+ p = pattern in
  optional space
  >>
  let+ t = ty in
  optional space
  >>
  let+ e = func in
  optional space >> string "in"
  >>
  let@ n = func in
  Ast.Let (p, t, e, n)


let rec nud s =
  (with_pos
     (let@ c = const in
      Ast.Const c)
  <|> with_pos (list_expr expr)
  <|> parens expr)
    s


and expr s = expression operators nud s
