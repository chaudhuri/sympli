signature RULES =
sig

  type table
  type rid

  val new : unit -> table
  val clear : table -> unit

  val rules : table -> Rule.rule list

  val add : table -> Rule.rule -> rid
  val rule : rid -> Rule.rule

  exception Invalid
  val del : rid -> unit

end

structure Rules :> RULES =
struct

type rule = Rule.rule

structure H = IntHashTable

type table = rule IntHashTable.hash_table
datatype rid = RID of {id : int,
                       rule : rule,
                       table : table}

val store = ref 0
fun fresh () = !store before store := !store + 1

fun rules tab = H.listItems tab

exception Invalid

fun new () = H.mkTable (128, Invalid)
val clear = H.clear

fun add tab r = 
    let
      val rid = fresh ()
    in
      H.insert tab (rid, r);
      RID {id = rid, rule = r, table = tab}
    end

open P.Desc

fun del (RID {table, id, ...}) =
      (H.remove table id;
       Comm.send "bsubs" (fn () => hBox [string " (* killed rule#", string (Int.toString id), string " *)"]))
      handle Invalid => ()

fun rule (RID {rule, ...}) = rule

end
