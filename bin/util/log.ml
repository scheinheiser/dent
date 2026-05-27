type t =
  | Debug of (src option * string)
  | Info of string
  | Warn of (Location.t option * string)
  | Error of (Location.t option * string)

and src = string * string * int * int * int

let comp_to_src func (f, l, s, e) = (f, func, l, s, e)

let fmt_debug src msg =
  match src with
  | Some (f, func, l, s, e) ->
      Format.asprintf
        "@[<v 2>[\x1b[1;33mDEBUG\x1b[0m]: %s@,file: %s@,function: %s@,loc: ln %d, chars %d-%d@]" msg
        f func l s e
  | None -> Format.asprintf "@[<v 2>\x1b[1;33m[DEBUG]\x1b[0m:@,%s@]" msg


let fmt_info msg = Format.asprintf "\x1b[1;94m[I@[<v>NFO]\x1b[0m:@,%s@]" msg

let fmt_warn loc msg =
  match loc with
  | Some l -> Format.asprintf "\x1b[1;33m[W@[<v>ARN]\x1b[0m %a:@,%s@]" Location.pp_location l msg
  | None -> Format.asprintf "\x1b[1;33m[W@[<v>ARN]\x1b[0m:@,%s@]" msg


let fmt_error loc msg =
  match loc with
  | Some l -> Format.asprintf "@[<v 2>%a@,\x1b[1;91m[E@[<v>RROR]\x1b[0m:%s@]@]" Location.pp_location l msg
  | None -> Format.asprintf "\x1b[1;91m[E@[<v>RROR]\x1b[0m:@,%s@]" msg


let log s =
  let msg =
    match s with
    | Debug (src, msg) -> fmt_debug src msg
    | Info msg -> fmt_info msg
    | Warn (loc, msg) -> fmt_warn loc msg
    | Error (loc, msg) -> fmt_error loc msg
  in
  print_endline msg

let dbg src msg = log @@ Debug (src, msg)
let info msg = log @@ Info msg
let warn w = log @@ Warn w
let err e = log @@ Error e
