open Util

type t = Location.t * token

and token =
  | INT of int
  | TY_INT
  | FLOAT of float
  | TY_FLOAT
  | STRING of string
  | TY_STRING
  | CHAR of char
  | TY_CHAR
  | BOOL of bool
  | TY_BOOL
  | UNIT
  | TY_UNIT
  | TY_ATOM
  | IDENT of string
  | UPPER_IDENT of string
  | DOT_SEP_IDENT of string list
  | OP of string
  | WHEN
  | WHERE
  | WITH
  | MATCH
  | TO
  | WITHOUT
  | RASSOC
  | LASSOC
  | IF
  | THEN
  | ELSE
  | DEC
  | TYPE
  | TILDE
  | DEF
  | FUN
  | LET
  | IN
  | END
  | MODULE
  | IMPORT
  | ALIAS
  | UNION
  | RECORD
  | CONSTRUCTOR
  | UNIVERSE
  | TTYPE
  | STAR
  | PIPE
  | LBRACE
  | RBRACE
  | LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | SEMI
  | SEMISEMI
  | COLON
  | EQ
  | ASSIGNMENT
  | ARROW
  | F_ARROW
  | ATSIGN
  | DOT
  | COMMA
  | BTICK
  | WILDCARD
  | EOF

let show (t : token) : string =
  let open Printf in
  match t with
  | INT i -> sprintf "INT %d" i
  | TY_INT -> sprintf "TY_INT"
  | FLOAT f -> sprintf "FLOAT %.5f" f
  | TY_FLOAT -> sprintf "TY_FLOAT"
  | STRING s -> sprintf "STRING \"%s\"" s
  | TY_STRING -> sprintf "TY_STRING"
  | CHAR c -> sprintf "CHAR %c" c
  | TY_CHAR -> sprintf "TY_CHAR"
  | BOOL b -> sprintf "BOOL %b" b
  | TY_BOOL -> sprintf "TY_BOOL"
  | UNIT -> "UNIT"
  | TY_UNIT -> "TY_UNIT"
  | TY_ATOM -> "TY_ATOM"
  | IDENT i -> sprintf "IDENT %s" i
  | UPPER_IDENT i -> sprintf "UPPER_IDENT %s" i
  | DOT_SEP_IDENT i -> sprintf "DOT_SEP_IDENT %s" (String.concat "." i)
  | OP o -> sprintf "OP %s" o
  | WHEN -> "WHEN"
  | WHERE -> "WHERE"
  | WITH -> "WITH"
  | MATCH -> "MATCH"
  | TO -> "TO"
  | WITHOUT -> "WITHOUT"
  | RASSOC -> "RASSOC"
  | LASSOC -> "LASSOC"
  | IF -> "IF"
  | THEN -> "THEN"
  | ELSE -> "ELSE"
  | DEC -> "DEC"
  | TYPE -> "TYPE"
  | TILDE -> "TILDE"
  | DEF -> "DEF"
  | FUN -> "FUN"
  | LET -> "LET"
  | IN -> "IN"
  | END -> "END"
  | MODULE -> "MODULE"
  | IMPORT -> "IMPORT"
  | ALIAS -> "ALIAS"
  | UNION -> "UNION"
  | RECORD -> "RECORD"
  | CONSTRUCTOR -> "CONSTRUCTOR"
  | UNIVERSE -> "UNIVERSE"
  | TTYPE -> "TTYPE"
  | STAR -> "STAR"
  | PIPE -> "PIPE"
  | LBRACE -> "LBRACE"
  | RBRACE -> "RBRACE"
  | LPAREN -> "LPAREN"
  | RPAREN -> "RPAREN"
  | LBRACK -> "LBRACK"
  | RBRACK -> "RBRACK"
  | SEMI -> "SEMI"
  | SEMISEMI -> "SEMISEMI"
  | COLON -> "COLON"
  | EQ -> "EQ"
  | ASSIGNMENT -> "ASSIGNMENT"
  | ARROW -> "ARROW"
  | F_ARROW -> "F_ARROW"
  | ATSIGN -> "ATSIGN"
  | DOT -> "DOT"
  | COMMA -> "COMMA"
  | BTICK -> "BTICK"
  | WILDCARD -> "WILDCARD"
  | EOF -> "EOF"
