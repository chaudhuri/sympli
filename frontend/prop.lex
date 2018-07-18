(* -*- mode: sml-lex; -*- *)

type pos = int * int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult  = (svalue,pos) token

datatype state =
         STATE of {nls : int list ref,      (* stack of newline positions *)
                   cur : int ref,           (* current line *)
                   comlev : int ref,        (* depth of comments *)
                   comst : int list ref}    (* start of comments *)

type arg = state

fun init () = STATE {nls = ref [1],
                     cur = ref 1,
                     comlev = ref 0,
                     comst = ref []}

fun lookup (a :: rest, cur) w =
      if a < w then (cur, w - a)
      else lookup (rest, cur - 1) w
  | lookup _ w = ErrorMsg.impossible' "undefined pos"

local open P.Desc in
fun newline (STATE {nls, cur, comlev, comst}) pos =
      (nls := pos :: (!nls);
       cur := !cur + 1)

fun tok (st as STATE {nls, cur, ...}) t (l, s) =
    let
      val r = l + String.size s
      val left = lookup (!nls, !cur) l
      val right = lookup (!nls, !cur) r
    in
      t (left, right)
    end

fun targ (st as STATE {nls, cur, ...}) t a (l, s) =
    let
      val r = l + String.size s
      val left = lookup (!nls, !cur) l
      val right = lookup (!nls, !cur) r
    in
      t (a, left, right)
    end
end

fun say s = print (s ^ "\n")

fun enter_comment (STATE {nls, cur, comlev, comst}) pos =
      (comlev := !comlev + 1;
       comst := pos :: (!comst))

(* [MOD] change exit_comment as needed if comments are to be preserved in extsyn *)
fun exit_comment (STATE {nls, cur, comlev, comst}) pos =
      (comlev := !comlev - 1;
       comst := List.tl (!comst))

fun in_comment (STATE {comlev, ...}) = !comlev > 0

exception LexError

fun eof (st as STATE {nls, cur, comst, comlev}) =
    if !comlev > 0 then
      (ErrorMsg.error' Mark.unknown "Unterminated comment"; raise LexError)
    else Tokens.EOF ((0, 0), (0, 0))

fun strip s = String.substring (s, 1, String.size s - 2)

fun trim s =
    List.hd (String.tokens Char.isSpace s)

%%
%header (functor PropLexFun (structure Tokens : Prop_TOKENS));

%full

%arg (state);
%s COMMENT LINCOM;

id = [A-Za-z][A-Za-z0-9_~!@#$%\^*+=\\|\'?/]*;
num = [0-9]+;
boolean = (true|false);

cbegin = "(*";
cend = "*)";

ws = [\ \t\012];

str = [^\']*;

%%

\n                   => (newline yyarg yypos; continue ());

<INITIAL>"%check"    => (tok yyarg Tokens.CHECK (yypos, yytext));
<INITIAL>"%reject"   => (tok yyarg Tokens.REJECT (yypos, yytext));
<INITIAL>"%norm"     => (tok yyarg Tokens.NORM (yypos, yytext));
<INITIAL>"%log"      => (tok yyarg Tokens.LOG (yypos, yytext));
<INITIAL>"%unlog"    => (tok yyarg Tokens.UNLOG (yypos, yytext));
<INITIAL>"%bind"     => (tok yyarg Tokens.BIND (yypos, yytext));
<INITIAL>"%channel"  => (tok yyarg Tokens.CHANNEL (yypos, yytext));
<INITIAL>"%include"  => (tok yyarg Tokens.INCLUDE (yypos, yytext));

<INITIAL>"% "        => (YYBEGIN LINCOM; continue ());
<LINCOM>.*           => (YYBEGIN INITIAL; continue ());

<INITIAL>{ws}+       => (continue ());

<INITIAL>"("         => (tok yyarg Tokens.LPAREN (yypos, yytext));
<INITIAL>")"         => (tok yyarg Tokens.RPAREN (yypos, yytext));
<INITIAL>"["         => (tok yyarg Tokens.LBRACK (yypos, yytext));
<INITIAL>"]"         => (tok yyarg Tokens.RBRACK (yypos, yytext));
<INITIAL>"{"         => (tok yyarg Tokens.LBRACE (yypos, yytext));
<INITIAL>"}"         => (tok yyarg Tokens.RBRACE (yypos, yytext));

<INITIAL>","         => (tok yyarg Tokens.COMMA (yypos, yytext));
<INITIAL>"."         => (tok yyarg Tokens.DOT (yypos, yytext));

<INITIAL>":"         => (tok yyarg Tokens.COLON (yypos, yytext));

<INITIAL>"`"         => (tok yyarg Tokens.TICK (yypos, yytext));
<INITIAL>";"         => (tok yyarg Tokens.SEMI (yypos, yytext));

<INITIAL>"*"         => (tok yyarg Tokens.STAR (yypos, yytext));
<INITIAL>"&"         => (tok yyarg Tokens.WITH (yypos, yytext));
<INITIAL>"o-o"       => (tok yyarg Tokens.LEQUIV (yypos, yytext));
<INITIAL>"-o"        => (tok yyarg Tokens.LOLLI (yypos, yytext));
<INITIAL>"o-"        => (tok yyarg Tokens.REVLOLLI (yypos, yytext));
<INITIAL>"+"         => (tok yyarg Tokens.CHOICE (yypos, yytext));

<INITIAL>"<->"       => (tok yyarg Tokens.EQUIV (yypos, yytext));
<INITIAL>"->"        => (tok yyarg Tokens.ARROW (yypos, yytext));
<INITIAL>"<-"        => (tok yyarg Tokens.REVARROW (yypos, yytext));

<INITIAL>"#"         => (tok yyarg Tokens.TOP (yypos, yytext));

<INITIAL>"!"         => (tok yyarg Tokens.BANG (yypos, yytext));

<INITIAL>"fst"       => (tok yyarg Tokens.FST (yypos, yytext));
<INITIAL>"snd"       => (tok yyarg Tokens.SND (yypos, yytext));
<INITIAL>"let"       => (tok yyarg Tokens.LET (yypos, yytext));
<INITIAL>"ulet"      => (tok yyarg Tokens.ULET (yypos, yytext));
<INITIAL>"="         => (tok yyarg Tokens.EQUALS (yypos, yytext));
<INITIAL>"in"        => (tok yyarg Tokens.IN (yypos, yytext));
<INITIAL>"end"       => (tok yyarg Tokens.END (yypos, yytext));
<INITIAL>"\\"        => (tok yyarg Tokens.LAM (yypos, yytext));
<INITIAL>"inl"       => (tok yyarg Tokens.INL (yypos, yytext));
<INITIAL>"inr"       => (tok yyarg Tokens.INR (yypos, yytext));
<INITIAL>"case"      => (tok yyarg Tokens.CASE (yypos, yytext));
<INITIAL>"of"        => (tok yyarg Tokens.OF (yypos, yytext));
<INITIAL>"|"         => (tok yyarg Tokens.BAR (yypos, yytext));
<INITIAL>"=>"        => (tok yyarg Tokens.DARROW (yypos, yytext));
<INITIAL>"abort"     => (tok yyarg Tokens.ABORT (yypos, yytext));


<INITIAL>"%axiom"     => (tok yyarg Tokens.AXIOM (yypos, yytext));
<INITIAL>"%theorem"   => (tok yyarg Tokens.THEOREM (yypos, yytext));
<INITIAL>"%left"      => (tok yyarg Tokens.LEFT (yypos, yytext));
<INITIAL>"%right"     => (tok yyarg Tokens.RIGHT (yypos, yytext));
<INITIAL>"%lemma"     => (tok yyarg Tokens.LEMMA (yypos, yytext));
<INITIAL>"%prove"     => (tok yyarg Tokens.PROVE (yypos, yytext));
<INITIAL>"%refute"    => (tok yyarg Tokens.REFUTE (yypos, yytext));
<INITIAL>"%constant"  => (tok yyarg Tokens.CONSTANT (yypos, yytext));
<INITIAL>"%prop"      => (tok yyarg Tokens.PROP (yypos, yytext));
<INITIAL>"%type"      => (tok yyarg Tokens.TYPE (yypos, yytext));

<INITIAL>{num}       => (case Int.fromString yytext of
                            SOME n => targ yyarg Tokens.NUM n (yypos, yytext)
                          | NONE => (ErrorMsg.error' Mark.unknown "cannot parse number; replacing with 0";
                                     targ yyarg Tokens.NUM 0 (yypos, yytext)));

<INITIAL>{boolean}   => (case Bool.fromString yytext of
                            SOME b => targ yyarg Tokens.BOOL b (yypos, yytext)
                          | NONE => (ErrorMsg.error' Mark.unknown "cannot parse boolean; replacing with false";
                                     targ yyarg Tokens.BOOL false (yypos, yytext)));

<INITIAL>{id}        => (targ yyarg Tokens.ID yytext (yypos, yytext));

<INITIAL>"'"{str}"'" => (targ yyarg Tokens.LIT (strip yytext) (yypos, yytext));

<INITIAL>{cbegin}    => (YYBEGIN COMMENT; enter_comment yyarg yypos; continue ());
<INITIAL>{cend}      => (ErrorMsg.error' Mark.unknown "Unbalanced comments"; continue ());

<COMMENT>{cbegin}    => (enter_comment yyarg yypos; continue ());
<COMMENT>{cend}      => (exit_comment yyarg yypos;
                         if not (in_comment yyarg) then YYBEGIN INITIAL else ();
                         continue ());

<COMMENT>.           => (continue ());

<INITIAL>.           => (ErrorMsg.error' Mark.unknown ("illegal character: \"" ^ yytext ^ "\""); continue ());
