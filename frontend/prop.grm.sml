functor PropLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : Prop_TOKENS
   end
 = 
struct
structure ParserData=
struct
structure Header = 
struct
(*#line 1.2 "prop.grm"*)structure ES = ExtSyn

exception Parse

open Prop
val ` = Prop

local open P.Desc in
fun inf (Proof.Inf i) _ = i
  | inf c (file, l, r) =
                (ErrorMsg.error (Mark.mark {left = l, right = r, file = file})
                                (hBox [Proof.pp_chk c, string " not an inferable term"]);
                 raise Parse)
end


(*#line 27.1 "prop.grm.sml"*)
end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\000\000\000\000\
\\001\000\002\000\044\000\003\000\081\000\004\000\043\000\006\000\042\000\
\\024\000\041\000\025\000\040\000\026\000\039\000\027\000\038\000\
\\028\000\037\000\032\000\036\000\033\000\035\000\034\000\034\000\
\\035\000\033\000\039\000\032\000\058\000\031\000\061\000\030\000\000\000\
\\001\000\002\000\044\000\004\000\043\000\006\000\042\000\024\000\041\000\
\\025\000\040\000\026\000\039\000\027\000\038\000\028\000\037\000\
\\032\000\036\000\033\000\035\000\034\000\034\000\035\000\033\000\
\\039\000\032\000\058\000\031\000\061\000\030\000\000\000\
\\001\000\002\000\053\000\006\000\052\000\023\000\051\000\024\000\050\000\
\\058\000\049\000\061\000\048\000\000\000\
\\001\000\002\000\053\000\006\000\052\000\023\000\051\000\024\000\050\000\
\\058\000\055\000\061\000\048\000\000\000\
\\001\000\003\000\200\000\007\000\200\000\009\000\200\000\014\000\092\000\
\\015\000\091\000\016\000\090\000\017\000\089\000\019\000\087\000\
\\020\000\086\000\021\000\085\000\000\000\
\\001\000\003\000\203\000\007\000\203\000\009\000\203\000\014\000\092\000\
\\015\000\091\000\016\000\090\000\017\000\089\000\019\000\087\000\
\\020\000\086\000\021\000\085\000\000\000\
\\001\000\003\000\114\000\008\000\113\000\014\000\064\000\000\000\
\\001\000\003\000\128\000\014\000\092\000\015\000\091\000\016\000\090\000\
\\017\000\089\000\018\000\088\000\019\000\087\000\020\000\086\000\
\\021\000\085\000\022\000\084\000\000\000\
\\001\000\003\000\148\000\014\000\064\000\000\000\
\\001\000\005\000\112\000\014\000\064\000\000\000\
\\001\000\006\000\074\000\024\000\073\000\058\000\072\000\061\000\071\000\000\000\
\\001\000\007\000\111\000\014\000\064\000\000\000\
\\001\000\007\000\127\000\014\000\092\000\015\000\091\000\016\000\090\000\
\\017\000\089\000\018\000\088\000\019\000\087\000\020\000\086\000\
\\021\000\085\000\022\000\084\000\000\000\
\\001\000\007\000\139\000\000\000\
\\001\000\009\000\020\000\000\000\
\\001\000\009\000\104\000\000\000\
\\001\000\010\000\061\000\000\000\
\\001\000\010\000\062\000\000\000\
\\001\000\010\000\082\000\014\000\064\000\000\000\
\\001\000\010\000\083\000\014\000\064\000\000\000\
\\001\000\010\000\097\000\000\000\
\\001\000\010\000\098\000\000\000\
\\001\000\014\000\064\000\030\000\142\000\000\000\
\\001\000\014\000\064\000\030\000\143\000\000\000\
\\001\000\014\000\064\000\030\000\145\000\000\000\
\\001\000\014\000\064\000\030\000\154\000\000\000\
\\001\000\014\000\064\000\030\000\159\000\000\000\
\\001\000\014\000\064\000\030\000\162\000\000\000\
\\001\000\014\000\064\000\031\000\157\000\000\000\
\\001\000\014\000\064\000\031\000\158\000\000\000\
\\001\000\014\000\064\000\031\000\160\000\000\000\
\\001\000\014\000\064\000\031\000\165\000\000\000\
\\001\000\014\000\064\000\031\000\168\000\000\000\
\\001\000\014\000\064\000\031\000\169\000\000\000\
\\001\000\014\000\064\000\036\000\103\000\000\000\
\\001\000\014\000\064\000\037\000\163\000\000\000\
\\001\000\014\000\107\000\029\000\106\000\000\000\
\\001\000\029\000\105\000\000\000\
\\001\000\029\000\108\000\000\000\
\\001\000\029\000\138\000\000\000\
\\001\000\029\000\144\000\000\000\
\\001\000\029\000\147\000\000\000\
\\001\000\033\000\132\000\000\000\
\\001\000\034\000\167\000\000\000\
\\001\000\038\000\149\000\000\000\
\\001\000\038\000\171\000\000\000\
\\001\000\060\000\022\000\000\000\
\\001\000\060\000\100\000\000\000\
\\001\000\061\000\023\000\000\000\
\\001\000\061\000\024\000\000\000\
\\001\000\061\000\025\000\000\000\
\\001\000\061\000\026\000\000\000\
\\001\000\061\000\056\000\000\000\
\\001\000\061\000\057\000\000\000\
\\001\000\061\000\059\000\000\000\
\\001\000\061\000\069\000\000\000\
\\001\000\061\000\070\000\000\000\
\\001\000\061\000\101\000\000\000\
\\001\000\061\000\109\000\000\000\
\\001\000\061\000\110\000\000\000\
\\001\000\061\000\136\000\000\000\
\\001\000\061\000\141\000\000\000\
\\001\000\061\000\170\000\000\000\
\\174\000\000\000\
\\175\000\040\000\019\000\041\000\018\000\042\000\017\000\043\000\016\000\
\\045\000\015\000\046\000\014\000\050\000\013\000\051\000\012\000\
\\052\000\011\000\053\000\010\000\054\000\009\000\055\000\008\000\
\\056\000\007\000\057\000\006\000\000\000\
\\176\000\000\000\
\\177\000\000\000\
\\178\000\014\000\092\000\015\000\091\000\016\000\090\000\017\000\089\000\
\\018\000\088\000\019\000\087\000\020\000\086\000\021\000\085\000\
\\022\000\084\000\000\000\
\\179\000\014\000\092\000\015\000\091\000\016\000\090\000\017\000\089\000\
\\018\000\088\000\019\000\087\000\020\000\086\000\021\000\085\000\
\\022\000\084\000\000\000\
\\180\000\000\000\
\\181\000\000\000\
\\182\000\014\000\092\000\015\000\091\000\016\000\090\000\017\000\089\000\
\\018\000\088\000\019\000\087\000\020\000\086\000\021\000\085\000\
\\022\000\084\000\000\000\
\\183\000\014\000\092\000\015\000\091\000\016\000\090\000\017\000\089\000\
\\018\000\088\000\019\000\087\000\020\000\086\000\021\000\085\000\
\\022\000\084\000\000\000\
\\184\000\014\000\092\000\015\000\091\000\016\000\090\000\017\000\089\000\
\\018\000\088\000\019\000\087\000\020\000\086\000\021\000\085\000\
\\022\000\084\000\000\000\
\\185\000\014\000\092\000\015\000\091\000\016\000\090\000\017\000\089\000\
\\018\000\088\000\019\000\087\000\020\000\086\000\021\000\085\000\
\\022\000\084\000\000\000\
\\186\000\014\000\092\000\015\000\091\000\016\000\090\000\017\000\089\000\
\\018\000\088\000\019\000\087\000\020\000\086\000\021\000\085\000\
\\022\000\084\000\000\000\
\\187\000\014\000\064\000\000\000\
\\188\000\000\000\
\\189\000\000\000\
\\190\000\000\000\
\\191\000\000\000\
\\192\000\000\000\
\\193\000\008\000\099\000\000\000\
\\194\000\000\000\
\\195\000\000\000\
\\196\000\000\000\
\\196\000\010\000\093\000\000\000\
\\197\000\000\000\
\\198\000\014\000\092\000\015\000\091\000\016\000\090\000\019\000\087\000\
\\020\000\086\000\000\000\
\\199\000\014\000\092\000\015\000\091\000\016\000\090\000\019\000\087\000\
\\020\000\086\000\000\000\
\\201\000\014\000\092\000\015\000\091\000\016\000\090\000\019\000\087\000\
\\020\000\086\000\000\000\
\\202\000\014\000\092\000\015\000\091\000\016\000\090\000\019\000\087\000\
\\020\000\086\000\000\000\
\\204\000\014\000\092\000\015\000\091\000\000\000\
\\205\000\014\000\092\000\000\000\
\\206\000\000\000\
\\207\000\000\000\
\\208\000\000\000\
\\209\000\000\000\
\\210\000\000\000\
\\211\000\000\000\
\\212\000\000\000\
\\213\000\000\000\
\\214\000\000\000\
\\215\000\000\000\
\\216\000\000\000\
\\217\000\014\000\064\000\000\000\
\\218\000\014\000\064\000\000\000\
\\219\000\000\000\
\\220\000\002\000\044\000\004\000\043\000\006\000\042\000\027\000\038\000\
\\028\000\037\000\058\000\031\000\061\000\030\000\000\000\
\\221\000\000\000\
\\222\000\000\000\
\\223\000\000\000\
\\224\000\000\000\
\\225\000\000\000\
\\226\000\000\000\
\\227\000\000\000\
\\228\000\000\000\
\\229\000\000\000\
\\230\000\000\000\
\\231\000\000\000\
\\232\000\000\000\
\\233\000\000\000\
\\234\000\000\000\
\"
val actionRowNumbers =
"\065\000\015\000\065\000\064\000\
\\047\000\049\000\050\000\051\000\
\\052\000\002\000\002\000\002\000\
\\003\000\004\000\053\000\054\000\
\\055\000\055\000\067\000\066\000\
\\082\000\081\000\017\000\079\000\
\\018\000\109\000\099\000\077\000\
\\111\000\113\000\002\000\002\000\
\\002\000\002\000\056\000\057\000\
\\011\000\002\000\002\000\002\000\
\\002\000\002\000\001\000\019\000\
\\020\000\073\000\085\000\087\000\
\\004\000\088\000\004\000\004\000\
\\072\000\086\000\021\000\022\000\
\\071\000\083\000\070\000\048\000\
\\058\000\110\000\002\000\108\000\
\\035\000\104\000\103\000\016\000\
\\038\000\037\000\039\000\059\000\
\\060\000\102\000\101\000\105\000\
\\012\000\010\000\007\000\116\000\
\\004\000\004\000\004\000\004\000\
\\004\000\004\000\004\000\004\000\
\\004\000\004\000\004\000\004\000\
\\096\000\013\000\008\000\004\000\
\\004\000\055\000\080\000\078\000\
\\100\000\043\000\002\000\002\000\
\\002\000\061\000\002\000\040\000\
\\014\000\121\000\122\000\002\000\
\\123\000\076\000\075\000\006\000\
\\092\000\091\000\093\000\005\000\
\\090\000\089\000\094\000\095\000\
\\074\000\097\000\098\000\069\000\
\\068\000\084\000\062\000\106\000\
\\023\000\024\000\041\000\025\000\
\\002\000\042\000\009\000\045\000\
\\002\000\002\000\002\000\002\000\
\\026\000\002\000\115\000\002\000\
\\029\000\030\000\027\000\031\000\
\\002\000\028\000\036\000\120\000\
\\119\000\002\000\114\000\032\000\
\\002\000\044\000\033\000\117\000\
\\034\000\063\000\112\000\118\000\
\\046\000\002\000\107\000\000\000"
val gotoT =
"\
\\001\000\171\000\002\000\003\000\003\000\002\000\004\000\001\000\000\000\
\\000\000\
\\002\000\019\000\003\000\002\000\004\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\027\000\007\000\026\000\008\000\025\000\000\000\
\\006\000\043\000\007\000\026\000\008\000\025\000\000\000\
\\006\000\044\000\007\000\026\000\008\000\025\000\000\000\
\\005\000\045\000\000\000\
\\005\000\052\000\000\000\
\\000\000\
\\000\000\
\\009\000\056\000\000\000\
\\009\000\058\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\061\000\008\000\025\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\063\000\007\000\026\000\008\000\025\000\000\000\
\\006\000\064\000\007\000\026\000\008\000\025\000\000\000\
\\006\000\065\000\007\000\026\000\008\000\025\000\000\000\
\\006\000\066\000\007\000\026\000\008\000\025\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\073\000\007\000\026\000\008\000\025\000\000\000\
\\006\000\074\000\007\000\026\000\008\000\025\000\000\000\
\\006\000\075\000\007\000\026\000\008\000\025\000\000\000\
\\006\000\076\000\007\000\026\000\008\000\025\000\000\000\
\\006\000\077\000\007\000\026\000\008\000\025\000\000\000\
\\006\000\078\000\007\000\026\000\008\000\025\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\092\000\000\000\
\\000\000\
\\005\000\093\000\000\000\
\\005\000\094\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\100\000\007\000\026\000\008\000\025\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\113\000\000\000\
\\005\000\114\000\000\000\
\\005\000\115\000\000\000\
\\005\000\116\000\000\000\
\\005\000\117\000\000\000\
\\005\000\118\000\000\000\
\\005\000\119\000\000\000\
\\005\000\120\000\000\000\
\\005\000\121\000\000\000\
\\005\000\122\000\000\000\
\\005\000\123\000\000\000\
\\005\000\124\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\127\000\000\000\
\\005\000\128\000\000\000\
\\009\000\129\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\131\000\007\000\026\000\008\000\025\000\000\000\
\\006\000\132\000\007\000\026\000\008\000\025\000\000\000\
\\006\000\133\000\007\000\026\000\008\000\025\000\000\000\
\\000\000\
\\006\000\135\000\007\000\026\000\008\000\025\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\138\000\007\000\026\000\008\000\025\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\144\000\007\000\026\000\008\000\025\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\148\000\007\000\026\000\008\000\025\000\000\000\
\\006\000\149\000\007\000\026\000\008\000\025\000\000\000\
\\006\000\150\000\007\000\026\000\008\000\025\000\000\000\
\\006\000\151\000\007\000\026\000\008\000\025\000\000\000\
\\000\000\
\\006\000\153\000\007\000\026\000\008\000\025\000\000\000\
\\000\000\
\\006\000\154\000\007\000\026\000\008\000\025\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\159\000\007\000\026\000\008\000\025\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\162\000\007\000\026\000\008\000\025\000\000\000\
\\000\000\
\\000\000\
\\006\000\164\000\007\000\026\000\008\000\025\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\170\000\007\000\026\000\008\000\025\000\000\000\
\\000\000\
\\000\000\
\"
val numstates = 172
val numrules = 61
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int*int
type arg = string
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit | ID of  (string) | LIT of  (string) | BOOL of  (bool) | NUM of  (int) | ids of  (string list) | aterm of  (Proof.chk) | app of  ( ( Proof.chk * pos * pos )  list) | term of  (Proof.chk) | prop of  (prop) | cmd of  (ExtSyn.cmd) | line of  ( ( ExtSyn.cmd * Mark.mark ) ) | lines of  ( ( ExtSyn.cmd * Mark.mark )  list) | theory of  ( ( ExtSyn.cmd * Mark.mark )  list)
end
type svalue = MlyValue.svalue
type result =  ( ExtSyn.cmd * Mark.mark )  list
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn (T 41) => true | (T 42) => true | (T 43) => true | (T 44) => true | (T 45) => true | (T 46) => true | (T 47) => true | (T 48) => true | (T 24) => true | (T 25) => true | (T 26) => true | (T 27) => true | (T 29) => true | (T 30) => true | (T 32) => true | (T 33) => true | (T 34) => true | (T 35) => true | (T 38) => true | (T 49) => true | (T 50) => true | (T 52) => true | (T 53) => true | (T 54) => true | (T 55) => true | (T 56) => true | _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn (T 0) => true | _ => false
val showTerminal =
fn (T 0) => "EOF"
  | (T 1) => "LPAREN"
  | (T 2) => "RPAREN"
  | (T 3) => "LBRACK"
  | (T 4) => "RBRACK"
  | (T 5) => "LBRACE"
  | (T 6) => "RBRACE"
  | (T 7) => "COMMA"
  | (T 8) => "DOT"
  | (T 9) => "COLON"
  | (T 10) => "TICK"
  | (T 11) => "SEMI"
  | (T 12) => "CARET"
  | (T 13) => "STAR"
  | (T 14) => "WITH"
  | (T 15) => "LOLLI"
  | (T 16) => "REVLOLLI"
  | (T 17) => "LEQUIV"
  | (T 18) => "CHOICE"
  | (T 19) => "ARROW"
  | (T 20) => "REVARROW"
  | (T 21) => "EQUIV"
  | (T 22) => "TOP"
  | (T 23) => "BANG"
  | (T 24) => "FST"
  | (T 25) => "SND"
  | (T 26) => "LET"
  | (T 27) => "ULET"
  | (T 28) => "EQUALS"
  | (T 29) => "IN"
  | (T 30) => "END"
  | (T 31) => "LAM"
  | (T 32) => "INL"
  | (T 33) => "INR"
  | (T 34) => "CASE"
  | (T 35) => "OF"
  | (T 36) => "BAR"
  | (T 37) => "DARROW"
  | (T 38) => "ABORT"
  | (T 39) => "LEFT"
  | (T 40) => "RIGHT"
  | (T 41) => "AXIOM"
  | (T 42) => "THEOREM"
  | (T 43) => "LEMMA"
  | (T 44) => "PROVE"
  | (T 45) => "REFUTE"
  | (T 46) => "CONSTANT"
  | (T 47) => "PROP"
  | (T 48) => "TYPE"
  | (T 49) => "CHECK"
  | (T 50) => "REJECT"
  | (T 51) => "NORM"
  | (T 52) => "LOG"
  | (T 53) => "UNLOG"
  | (T 54) => "BIND"
  | (T 55) => "CHANNEL"
  | (T 56) => "INCLUDE"
  | (T 57) => "NUM"
  | (T 58) => "BOOL"
  | (T 59) => "LIT"
  | (T 60) => "ID"
  | (T 61) => "UNARY"
  | (T 62) => "APPLY"
  | (T 63) => "LOW"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 63) $$ (T 62) $$ (T 61) $$ (T 56) $$ (T 55) $$ (T 54) $$ (T 53) $$ (T 52) $$ (T 51) $$ (T 50) $$ (T 49) $$ (T 48) $$ (T 47) $$ (T 46) $$ (T 45) $$ (T 44) $$ (T 43) $$ (T 42) $$ (T 41) $$ (T 40) $$ (T 39) $$ (T 38) $$ (T 37) $$ (T 36) $$ (T 35) $$ (T 34) $$ (T 33) $$ (T 32) $$ (T 31) $$ (T 30) $$ (T 29) $$ (T 28) $$ (T 27) $$ (T 26) $$ (T 25) $$ (T 24) $$ (T 23) $$ (T 22) $$ (T 21) $$ (T 20) $$ (T 19) $$ (T 18) $$ (T 17) $$ (T 16) $$ (T 15) $$ (T 14) $$ (T 13) $$ (T 12) $$ (T 11) $$ (T 10) $$ (T 9) $$ (T 8) $$ (T 7) $$ (T 6) $$ (T 5) $$ (T 4) $$ (T 3) $$ (T 2) $$ (T 1) $$ (T 0)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (file):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.lines lines, lines1left, lines1right)) :: rest671)) => let val  result = MlyValue.theory ((*#line 71.35 "prop.grm"*)lines(*#line 575.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 0, ( result, lines1left, lines1right), rest671)
end
|  ( 1, ( rest671)) => let val  result = MlyValue.lines ((*#line 73.35 "prop.grm"*)[](*#line 579.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 1, ( result, defaultPos, defaultPos), rest671)
end
|  ( 2, ( ( _, ( MlyValue.lines lines, _, lines1right)) :: ( _, ( MlyValue.line line, line1left, _)) :: rest671)) => let val  result = MlyValue.lines ((*#line 74.35 "prop.grm"*)line :: lines(*#line 583.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 1, ( result, line1left, lines1right), rest671)
end
|  ( 3, ( ( _, ( _, _, (DOTright as DOT1right))) :: ( _, ( MlyValue.cmd cmd, (cmdleft as cmd1left), _)) :: rest671)) => let val  result = MlyValue.line ((*#line 76.35 "prop.grm"*)(cmd, Mark.mark {left = cmdleft, right = DOTright, file = file})(*#line 587.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 2, ( result, cmd1left, DOT1right), rest671)
end
|  ( 4, ( ( _, ( MlyValue.prop prop, _, prop1right)) :: _ :: ( _, ( MlyValue.ID ID, _, _)) :: ( _, ( _, AXIOM1left, _)) :: rest671)) => let val  result = MlyValue.cmd ((*#line 78.35 "prop.grm"*)ES.Assume (ID, prop)(*#line 591.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, AXIOM1left, prop1right), rest671)
end
|  ( 5, ( ( _, ( MlyValue.prop prop, _, prop1right)) :: _ :: ( _, ( MlyValue.ID ID, _, _)) :: ( _, ( _, THEOREM1left, _)) :: rest671)) => let val  result = MlyValue.cmd ((*#line 79.35 "prop.grm"*)ES.Assume (ID, prop)(*#line 595.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, THEOREM1left, prop1right), rest671)
end
|  ( 6, ( ( _, ( MlyValue.ids ids, _, ids1right)) :: ( _, ( _, LEFT1left, _)) :: rest671)) => let val  result = MlyValue.cmd ((*#line 80.35 "prop.grm"*)ES.Left ids(*#line 599.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, LEFT1left, ids1right), rest671)
end
|  ( 7, ( ( _, ( MlyValue.ids ids, _, ids1right)) :: ( _, ( _, RIGHT1left, _)) :: rest671)) => let val  result = MlyValue.cmd ((*#line 81.35 "prop.grm"*)ES.Right ids(*#line 603.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, RIGHT1left, ids1right), rest671)
end
|  ( 8, ( ( _, ( MlyValue.prop prop, _, prop1right)) :: ( _, ( _, PROVE1left, _)) :: rest671)) => let val  result = MlyValue.cmd ((*#line 82.35 "prop.grm"*)ES.Prove (prop)(*#line 607.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, PROVE1left, prop1right), rest671)
end
|  ( 9, ( ( _, ( MlyValue.prop prop, _, prop1right)) :: ( _, ( _, REFUTE1left, _)) :: rest671)) => let val  result = MlyValue.cmd ((*#line 83.35 "prop.grm"*)ES.Refute (Option.getOpt (Int.maxInt, 99999), prop)(*#line 611.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, REFUTE1left, prop1right), rest671)
end
|  ( 10, ( ( _, ( MlyValue.prop prop, _, prop1right)) :: _ :: ( _, ( MlyValue.NUM NUM, _, _)) :: ( _, ( _, REFUTE1left, _)) :: rest671)) => let val  result = MlyValue.cmd ((*#line 84.35 "prop.grm"*)ES.Refute (NUM, prop)(*#line 615.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, REFUTE1left, prop1right), rest671)
end
|  ( 11, ( ( _, ( MlyValue.prop prop, _, prop1right)) :: _ :: ( _, ( MlyValue.term term, _, _)) :: ( _, ( _, CHECK1left, _)) :: rest671)) => let val  result = MlyValue.cmd ((*#line 85.35 "prop.grm"*)ES.Check (term, prop)(*#line 619.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, CHECK1left, prop1right), rest671)
end
|  ( 12, ( ( _, ( MlyValue.prop prop, _, prop1right)) :: _ :: ( _, ( MlyValue.term term, _, _)) :: ( _, ( _, REJECT1left, _)) :: rest671)) => let val  result = MlyValue.cmd ((*#line 86.35 "prop.grm"*)ES.Reject (term, prop)(*#line 623.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, REJECT1left, prop1right), rest671)
end
|  ( 13, ( ( _, ( MlyValue.term term, _, term1right)) :: ( _, ( _, NORM1left, _)) :: rest671)) => let val  result = MlyValue.cmd ((*#line 87.35 "prop.grm"*)ES.Norm term(*#line 627.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, NORM1left, term1right), rest671)
end
|  ( 14, ( ( _, ( MlyValue.ID ID2, _, ID2right)) :: _ :: ( _, ( MlyValue.ID ID1, _, _)) :: ( _, ( _, LOG1left, _)) :: rest671)) => let val  result = MlyValue.cmd ((*#line 88.35 "prop.grm"*)ES.Log (ID1, ID2)(*#line 631.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, LOG1left, ID2right), rest671)
end
|  ( 15, ( ( _, ( MlyValue.ID ID, _, ID1right)) :: ( _, ( _, UNLOG1left, _)) :: rest671)) => let val  result = MlyValue.cmd ((*#line 89.35 "prop.grm"*)ES.Unlog ID(*#line 635.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, UNLOG1left, ID1right), rest671)
end
|  ( 16, ( ( _, ( MlyValue.LIT LIT, _, LIT1right)) :: _ :: ( _, ( MlyValue.ID ID, _, _)) :: ( _, ( _, BIND1left, _)) :: rest671)) => let val  result = MlyValue.cmd ((*#line 90.35 "prop.grm"*)ES.Bind (ID, LIT)(*#line 639.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, BIND1left, LIT1right), rest671)
end
|  ( 17, ( ( _, ( MlyValue.ID ID, _, ID1right)) :: ( _, ( _, CHANNEL1left, _)) :: rest671)) => let val  result = MlyValue.cmd ((*#line 91.35 "prop.grm"*)ES.Channel ID(*#line 643.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, CHANNEL1left, ID1right), rest671)
end
|  ( 18, ( ( _, ( MlyValue.LIT LIT, _, LIT1right)) :: ( _, ( _, INCLUDE1left, _)) :: rest671)) => let val  result = MlyValue.cmd ((*#line 92.35 "prop.grm"*)ES.Include (LIT)(*#line 647.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, INCLUDE1left, LIT1right), rest671)
end
|  ( 19, ( ( _, ( MlyValue.ID ID, ID1left, ID1right)) :: rest671)) => let val  result = MlyValue.ids ((*#line 94.35 "prop.grm"*)[ID](*#line 651.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 8, ( result, ID1left, ID1right), rest671)
end
|  ( 20, ( ( _, ( MlyValue.ids ids, _, ids1right)) :: _ :: ( _, ( MlyValue.ID ID, ID1left, _)) :: rest671)) => let val  result = MlyValue.ids ((*#line 95.35 "prop.grm"*)ID :: ids(*#line 655.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 8, ( result, ID1left, ids1right), rest671)
end
|  ( 21, ( ( _, ( MlyValue.ID ID, ID1left, ID1right)) :: rest671)) => let val  result = MlyValue.prop ((*#line 97.35 "prop.grm"*)Prop (Prop.Atomic (Atom.atom ID))(*#line 659.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, ID1left, ID1right), rest671)
end
|  ( 22, ( ( _, ( MlyValue.NUM NUM, (NUMleft as NUM1left), (NUMright as NUM1right))) :: rest671)) => let val  result = MlyValue.prop ((*#line 98.35 "prop.grm"*)case NUM of
                                    0 => `Zero
                                  | 1 => `One
                                  | n => (ErrorMsg.error' (Mark.mark {left = NUMleft,
                                                                      right = NUMright,
                                                                      file = file})
                                                          ("unknown proposition: " ^ Int.toString n);
                                          raise Parse)(*#line 663.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, NUM1left, NUM1right), rest671)
end
|  ( 23, ( ( _, ( _, TOP1left, TOP1right)) :: rest671)) => let val  result = MlyValue.prop ((*#line 106.35 "prop.grm"*)`Top(*#line 674.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, TOP1left, TOP1right), rest671)
end
|  ( 24, ( ( _, ( MlyValue.prop prop2, _, prop2right)) :: _ :: ( _, ( MlyValue.prop prop1, prop1left, _)) :: rest671)) => let val  result = MlyValue.prop ((*#line 107.35 "prop.grm"*)Prop (Limp (prop1, prop2))(*#line 678.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, prop1left, prop2right), rest671)
end
|  ( 25, ( ( _, ( MlyValue.prop prop2, _, prop2right)) :: _ :: ( _, ( MlyValue.prop prop1, prop1left, _)) :: rest671)) => let val  result = MlyValue.prop ((*#line 108.35 "prop.grm"*)Prop (Limp (prop2, prop1))(*#line 682.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, prop1left, prop2right), rest671)
end
|  ( 26, ( ( _, ( MlyValue.prop prop2, _, prop2right)) :: _ :: ( _, ( MlyValue.prop prop1, prop1left, _)) :: rest671)) => let val  result = MlyValue.prop ((*#line 109.35 "prop.grm"*)Prop (With (Prop (Limp (prop1, prop2)),
                                              Prop (Limp (prop2, prop1))))(*#line 686.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, prop1left, prop2right), rest671)
end
|  ( 27, ( ( _, ( MlyValue.prop prop2, _, prop2right)) :: _ :: ( _, ( MlyValue.prop prop1, prop1left, _)) :: rest671)) => let val  result = MlyValue.prop ((*#line 111.35 "prop.grm"*)Prop (Limp (Prop (Bang prop1), prop2))(*#line 691.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, prop1left, prop2right), rest671)
end
|  ( 28, ( ( _, ( MlyValue.prop prop2, _, prop2right)) :: _ :: ( _, ( MlyValue.prop prop1, prop1left, _)) :: rest671)) => let val  result = MlyValue.prop ((*#line 112.35 "prop.grm"*)Prop (Limp (Prop (Bang prop2), prop1))(*#line 695.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, prop1left, prop2right), rest671)
end
|  ( 29, ( ( _, ( MlyValue.prop prop2, _, prop2right)) :: _ :: ( _, ( MlyValue.prop prop1, prop1left, _)) :: rest671)) => let val  result = MlyValue.prop ((*#line 113.35 "prop.grm"*)Prop (With (Prop (Limp (Prop (Bang prop1), prop2)),
                                              Prop (Limp (Prop (Bang prop2), prop1))))(*#line 699.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, prop1left, prop2right), rest671)
end
|  ( 30, ( ( _, ( MlyValue.prop prop2, _, prop2right)) :: _ :: ( _, ( MlyValue.prop prop1, prop1left, _)) :: rest671)) => let val  result = MlyValue.prop ((*#line 115.35 "prop.grm"*)Prop (Choice (prop1, prop2))(*#line 704.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, prop1left, prop2right), rest671)
end
|  ( 31, ( ( _, ( MlyValue.prop prop2, _, prop2right)) :: _ :: ( _, ( MlyValue.prop prop1, prop1left, _)) :: rest671)) => let val  result = MlyValue.prop ((*#line 116.35 "prop.grm"*)Prop (With (prop1, prop2))(*#line 708.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, prop1left, prop2right), rest671)
end
|  ( 32, ( ( _, ( MlyValue.prop prop2, _, prop2right)) :: _ :: ( _, ( MlyValue.prop prop1, prop1left, _)) :: rest671)) => let val  result = MlyValue.prop ((*#line 117.35 "prop.grm"*)Prop (Tensor (prop1, prop2))(*#line 712.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, prop1left, prop2right), rest671)
end
|  ( 33, ( ( _, ( MlyValue.prop prop, _, prop1right)) :: ( _, ( _, BANG1left, _)) :: rest671)) => let val  result = MlyValue.prop ((*#line 118.35 "prop.grm"*)Prop (Bang prop)(*#line 716.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, BANG1left, prop1right), rest671)
end
|  ( 34, ( ( _, ( _, _, RBRACE1right)) :: ( _, ( MlyValue.prop prop, _, _)) :: ( _, ( _, LBRACE1left, _)) :: rest671)) => let val  result = MlyValue.prop ((*#line 119.35 "prop.grm"*)Prop (Brace prop)(*#line 720.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, LBRACE1left, RBRACE1right), rest671)
end
|  ( 35, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.prop prop, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result = MlyValue.prop ((*#line 120.35 "prop.grm"*)prop(*#line 724.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 36, ( ( _, ( MlyValue.app app, app1left, app1right)) :: rest671)) => let val  result = MlyValue.term ((*#line 122.37 "prop.grm"*)case app of
                                      [(t, _, _)] => t
                                    | (h, hl, hr) :: S =>
                                      let
                                        val h = inf h (file, hl, hr)
                                      in
                                        Proof.Inf (List.foldl (fn ((c, _, _), h) => Proof.App (h, c)) h S)
                                      end(*#line 728.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, app1left, app1right), rest671)
end
|  ( 37, ( ( _, ( MlyValue.term term2, _, term2right)) :: _ :: ( _, ( MlyValue.term term1, term1left, _)) :: rest671)) => let val  result = MlyValue.term ((*#line 130.37 "prop.grm"*)Proof.Tensor (term1, term2)(*#line 739.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, term1left, term2right), rest671)
end
|  ( 38, ( ( _, ( MlyValue.term term, termleft, (termright as term1right))) :: ( _, ( _, FST1left, _)) :: rest671)) => let val  result = MlyValue.term ((*#line 131.37 "prop.grm"*)Proof.Inf (Proof.Fst (inf term (file, termleft, termright)))(*#line 743.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, FST1left, term1right), rest671)
end
|  ( 39, ( ( _, ( MlyValue.term term, termleft, (termright as term1right))) :: ( _, ( _, SND1left, _)) :: rest671)) => let val  result = MlyValue.term ((*#line 132.37 "prop.grm"*)Proof.Inf (Proof.Snd (inf term (file, termleft, termright)))(*#line 747.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, SND1left, term1right), rest671)
end
|  ( 40, ( ( _, ( MlyValue.term term, _, term1right)) :: ( _, ( _, INL1left, _)) :: rest671)) => let val  result = MlyValue.term ((*#line 133.37 "prop.grm"*)Proof.Inl term(*#line 751.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, INL1left, term1right), rest671)
end
|  ( 41, ( ( _, ( MlyValue.term term, _, term1right)) :: ( _, ( _, INR1left, _)) :: rest671)) => let val  result = MlyValue.term ((*#line 134.37 "prop.grm"*)Proof.Inr term(*#line 755.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, INR1left, term1right), rest671)
end
|  ( 42, ( ( _, ( MlyValue.term term, _, term1right)) :: ( _, ( _, BANG1left, _)) :: rest671)) => let val  result = MlyValue.term ((*#line 135.37 "prop.grm"*)Proof.Bang term(*#line 759.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, BANG1left, term1right), rest671)
end
|  ( 43, ( ( _, ( MlyValue.term term, _, term1right)) :: _ :: ( _, ( MlyValue.ID ID, _, _)) :: ( _, ( _, LAM1left, _)) :: rest671)) => let val  result = MlyValue.term ((*#line 136.37 "prop.grm"*)Proof.Lam (Var.named ID, term)(*#line 763.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, LAM1left, term1right), rest671)
end
|  ( 44, ( ( _, ( MlyValue.term term3, _, term3right)) :: _ :: ( _, ( MlyValue.ID ID2, _, _)) :: _ :: _ :: ( _, ( MlyValue.term term2, _, _)) :: _ :: ( _, ( MlyValue.ID ID1, _, _)) :: _ :: _ :: ( _, ( MlyValue.term term1, term1left, term1right)) :: ( _, ( _, CASE1left, _)) :: rest671)) => let val  result = MlyValue.term ((*#line 138.37 "prop.grm"*)Proof.Case (inf term1 (file, term1left, term1right),
                                                (Var.named ID1, term2), (Var.named ID2, term3))(*#line 767.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, CASE1left, term3right), rest671)
end
|  ( 45, ( ( _, ( MlyValue.term term, termleft, (termright as term1right))) :: ( _, ( _, ABORT1left, _)) :: rest671)) => let val  result = MlyValue.term ((*#line 140.37 "prop.grm"*)Proof.Abort (inf term (file, termleft, termright))(*#line 772.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, ABORT1left, term1right), rest671)
end
|  ( 46, ( ( _, ( MlyValue.aterm aterm, (atermleft as aterm1left), (atermright as aterm1right))) :: rest671)) => let val  result = MlyValue.app ((*#line 142.37 "prop.grm"*)[(aterm, atermleft, atermright)](*#line 776.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 6, ( result, aterm1left, aterm1right), rest671)
end
|  ( 47, ( ( _, ( MlyValue.app app, _, app1right)) :: ( _, ( MlyValue.aterm aterm, (atermleft as aterm1left), atermright)) :: rest671)) => let val  result = MlyValue.app ((*#line 143.37 "prop.grm"*)(aterm, atermleft, atermright) :: app(*#line 780.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 6, ( result, aterm1left, app1right), rest671)
end
|  ( 48, ( ( _, ( MlyValue.ID ID, ID1left, ID1right)) :: rest671)) => let val  result = MlyValue.aterm ((*#line 145.50 "prop.grm"*)Proof.Inf (Proof.Var (Var.named ID))(*#line 784.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 7, ( result, ID1left, ID1right), rest671)
end
|  ( 49, ( ( _, ( _, _, END1right)) :: ( _, ( MlyValue.term term2, _, _)) :: _ :: ( _, ( MlyValue.term term1, term1left, term1right)) :: _ :: ( _, ( MlyValue.ID ID2, _, _)) :: _ :: ( _, ( MlyValue.ID ID1, _, _)) :: ( _, ( _, LET1left, _)) :: rest671)) => let val  result = MlyValue.aterm ((*#line 147.50 "prop.grm"*)Proof.LetTens (inf term1 (file, term1left, term1right),
                                                                ((Var.named ID1, Var.named ID2), term2))(*#line 788.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 7, ( result, LET1left, END1right), rest671)
end
|  ( 50, ( ( _, ( MlyValue.NUM NUM, (NUMleft as NUM1left), (NUMright as NUM1right))) :: rest671)) => let val  result = MlyValue.aterm ((*#line 149.50 "prop.grm"*)case NUM of
                                                   1 => Proof.One
                                                 | n => (ErrorMsg.error' (Mark.mark {left = NUMleft,
                                                                                     right = NUMright,
                                                                                     file = file})
                                                                         ("unknown numerical constant: "
                                                                          ^ Int.toString n);
                                                          raise Parse)(*#line 793.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 7, ( result, NUM1left, NUM1right), rest671)
end
|  ( 51, ( ( _, ( _, _, END1right)) :: ( _, ( MlyValue.term term2, _, _)) :: _ :: ( _, ( MlyValue.term term1, term1left, term1right)) :: _ :: _ :: ( _, ( _, LET1left, _)) :: rest671)) => let val  result = MlyValue.aterm ((*#line 158.50 "prop.grm"*)Proof.LetOne (inf term1 (file, term1left, term1right),
                                                               term2)(*#line 804.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 7, ( result, LET1left, END1right), rest671)
end
|  ( 52, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.term term2, _, _)) :: _ :: ( _, ( MlyValue.term term1, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result = MlyValue.aterm ((*#line 161.50 "prop.grm"*)Proof.Pair (term1, term2)(*#line 809.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 7, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 53, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result = MlyValue.aterm ((*#line 162.50 "prop.grm"*)Proof.Unit(*#line 813.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 7, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 54, ( ( _, ( _, _, END1right)) :: ( _, ( MlyValue.term term2, _, _)) :: _ :: ( _, ( MlyValue.term term1, term1left, term1right)) :: _ :: ( _, ( MlyValue.ID ID, _, _)) :: _ :: ( _, ( _, LET1left, _)) :: rest671)) => let val  result = MlyValue.aterm ((*#line 164.50 "prop.grm"*)Proof.LetBang (inf term1 (file, term1left, term1right),
                                                                (Var.named ID, term2))(*#line 817.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 7, ( result, LET1left, END1right), rest671)
end
|  ( 55, ( ( _, ( _, _, END1right)) :: ( _, ( MlyValue.term term2, _, _)) :: _ :: ( _, ( MlyValue.term term1, term1left, term1right)) :: _ :: _ :: ( _, ( MlyValue.ID ID, _, _)) :: _ :: ( _, ( _, LET1left, _)) :: rest671)) => let val  result = MlyValue.aterm ((*#line 167.50 "prop.grm"*)Proof.LetBra (inf term1 (file, term1left, term1right),
                                                               (Var.named ID, term2))(*#line 822.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 7, ( result, LET1left, END1right), rest671)
end
|  ( 56, ( ( _, ( _, _, END1right)) :: ( _, ( MlyValue.term term2, _, _)) :: _ :: ( _, ( MlyValue.term term1, term1left, term1right)) :: _ :: ( _, ( MlyValue.ID ID, _, _)) :: ( _, ( _, LET1left, _)) :: rest671)) => let val  result = MlyValue.aterm ((*#line 169.50 "prop.grm"*)Proof.Let (inf term1 (file, term1left, term1right),
                                                            (Var.named ID, term2))(*#line 827.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 7, ( result, LET1left, END1right), rest671)
end
|  ( 57, ( ( _, ( _, _, END1right)) :: ( _, ( MlyValue.term term2, _, _)) :: _ :: ( _, ( MlyValue.term term1, term1left, term1right)) :: _ :: ( _, ( MlyValue.ID ID, _, _)) :: ( _, ( _, ULET1left, _)) :: rest671)) => let val  result = MlyValue.aterm ((*#line 171.50 "prop.grm"*)Proof.Ulet (inf term1 (file, term1left, term1right),
                                                             (Var.named ID, term2))(*#line 832.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 7, ( result, ULET1left, END1right), rest671)
end
|  ( 58, ( ( _, ( _, _, RBRACE1right)) :: ( _, ( MlyValue.term term, _, _)) :: ( _, ( _, LBRACE1left, _)) :: rest671)) => let val  result = MlyValue.aterm ((*#line 173.50 "prop.grm"*)Proof.Bra term(*#line 837.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 7, ( result, LBRACE1left, RBRACE1right), rest671)
end
|  ( 59, ( ( _, ( _, _, RBRACK1right)) :: ( _, ( MlyValue.term term, _, _)) :: ( _, ( _, LBRACK1left, _)) :: rest671)) => let val  result = MlyValue.aterm ((*#line 174.50 "prop.grm"*)Proof.Inf (Proof.Chk term)(*#line 841.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 7, ( result, LBRACK1left, RBRACK1right), rest671)
end
|  ( 60, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.term term, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result = MlyValue.aterm ((*#line 177.50 "prop.grm"*)term(*#line 845.1 "prop.grm.sml"*)
)
 in ( LrTable.NT 7, ( result, LPAREN1left, RPAREN1right), rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.theory x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a 
end
end
structure Tokens : Prop_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(ParserData.MlyValue.VOID,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(ParserData.MlyValue.VOID,p1,p2))
fun LBRACK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(ParserData.MlyValue.VOID,p1,p2))
fun RBRACK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(ParserData.MlyValue.VOID,p1,p2))
fun LBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(ParserData.MlyValue.VOID,p1,p2))
fun RBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(ParserData.MlyValue.VOID,p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(ParserData.MlyValue.VOID,p1,p2))
fun DOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(ParserData.MlyValue.VOID,p1,p2))
fun COLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(ParserData.MlyValue.VOID,p1,p2))
fun TICK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(ParserData.MlyValue.VOID,p1,p2))
fun SEMI (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(ParserData.MlyValue.VOID,p1,p2))
fun CARET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(ParserData.MlyValue.VOID,p1,p2))
fun STAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(ParserData.MlyValue.VOID,p1,p2))
fun WITH (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(ParserData.MlyValue.VOID,p1,p2))
fun LOLLI (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(ParserData.MlyValue.VOID,p1,p2))
fun REVLOLLI (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(ParserData.MlyValue.VOID,p1,p2))
fun LEQUIV (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(ParserData.MlyValue.VOID,p1,p2))
fun CHOICE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(ParserData.MlyValue.VOID,p1,p2))
fun ARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(ParserData.MlyValue.VOID,p1,p2))
fun REVARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(ParserData.MlyValue.VOID,p1,p2))
fun EQUIV (p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(ParserData.MlyValue.VOID,p1,p2))
fun TOP (p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(ParserData.MlyValue.VOID,p1,p2))
fun BANG (p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(ParserData.MlyValue.VOID,p1,p2))
fun FST (p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(ParserData.MlyValue.VOID,p1,p2))
fun SND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 25,(ParserData.MlyValue.VOID,p1,p2))
fun LET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 26,(ParserData.MlyValue.VOID,p1,p2))
fun ULET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 27,(ParserData.MlyValue.VOID,p1,p2))
fun EQUALS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 28,(ParserData.MlyValue.VOID,p1,p2))
fun IN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 29,(ParserData.MlyValue.VOID,p1,p2))
fun END (p1,p2) = Token.TOKEN (ParserData.LrTable.T 30,(ParserData.MlyValue.VOID,p1,p2))
fun LAM (p1,p2) = Token.TOKEN (ParserData.LrTable.T 31,(ParserData.MlyValue.VOID,p1,p2))
fun INL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 32,(ParserData.MlyValue.VOID,p1,p2))
fun INR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 33,(ParserData.MlyValue.VOID,p1,p2))
fun CASE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 34,(ParserData.MlyValue.VOID,p1,p2))
fun OF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 35,(ParserData.MlyValue.VOID,p1,p2))
fun BAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 36,(ParserData.MlyValue.VOID,p1,p2))
fun DARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 37,(ParserData.MlyValue.VOID,p1,p2))
fun ABORT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 38,(ParserData.MlyValue.VOID,p1,p2))
fun LEFT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 39,(ParserData.MlyValue.VOID,p1,p2))
fun RIGHT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 40,(ParserData.MlyValue.VOID,p1,p2))
fun AXIOM (p1,p2) = Token.TOKEN (ParserData.LrTable.T 41,(ParserData.MlyValue.VOID,p1,p2))
fun THEOREM (p1,p2) = Token.TOKEN (ParserData.LrTable.T 42,(ParserData.MlyValue.VOID,p1,p2))
fun LEMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 43,(ParserData.MlyValue.VOID,p1,p2))
fun PROVE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 44,(ParserData.MlyValue.VOID,p1,p2))
fun REFUTE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 45,(ParserData.MlyValue.VOID,p1,p2))
fun CONSTANT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 46,(ParserData.MlyValue.VOID,p1,p2))
fun PROP (p1,p2) = Token.TOKEN (ParserData.LrTable.T 47,(ParserData.MlyValue.VOID,p1,p2))
fun TYPE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 48,(ParserData.MlyValue.VOID,p1,p2))
fun CHECK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 49,(ParserData.MlyValue.VOID,p1,p2))
fun REJECT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 50,(ParserData.MlyValue.VOID,p1,p2))
fun NORM (p1,p2) = Token.TOKEN (ParserData.LrTable.T 51,(ParserData.MlyValue.VOID,p1,p2))
fun LOG (p1,p2) = Token.TOKEN (ParserData.LrTable.T 52,(ParserData.MlyValue.VOID,p1,p2))
fun UNLOG (p1,p2) = Token.TOKEN (ParserData.LrTable.T 53,(ParserData.MlyValue.VOID,p1,p2))
fun BIND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 54,(ParserData.MlyValue.VOID,p1,p2))
fun CHANNEL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 55,(ParserData.MlyValue.VOID,p1,p2))
fun INCLUDE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 56,(ParserData.MlyValue.VOID,p1,p2))
fun NUM (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 57,(ParserData.MlyValue.NUM i,p1,p2))
fun BOOL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 58,(ParserData.MlyValue.BOOL i,p1,p2))
fun LIT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 59,(ParserData.MlyValue.LIT i,p1,p2))
fun ID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 60,(ParserData.MlyValue.ID i,p1,p2))
fun UNARY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 61,(ParserData.MlyValue.VOID,p1,p2))
fun APPLY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 62,(ParserData.MlyValue.VOID,p1,p2))
fun LOW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 63,(ParserData.MlyValue.VOID,p1,p2))
end
end
