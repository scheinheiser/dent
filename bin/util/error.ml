type t = Location.t option * string

exception InternalError of string
exception Todo of string

let todo m = raise (Todo m)

let pp_err out ((loc, msg) : t) =
  match loc with
  | Some l ->
    Format.fprintf out "[E@[<v>RROR] %a:@,%s@]@." Location.pp_location l msg
  | None -> Format.fprintf out "[E@[<v>RROR]:@,%s@]@." msg

let pp_warning out ((loc, msg) : t) =
  match loc with
  | Some l -> Format.fprintf out "[WARNING] %a; %s@." Location.pp_location l msg
  | None -> Format.fprintf out "[WARNING]: %s@." msg

let format_err (err : t) : string = Format.asprintf "%a" pp_err err

let report_err err =
  pp_err Format.err_formatter err;
  exit 1
