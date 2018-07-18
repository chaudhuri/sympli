signature Prop_TOKENS =
sig
type ('a,'b) token
type svalue
val LOW:  'a * 'a -> (svalue,'a) token
val APPLY:  'a * 'a -> (svalue,'a) token
val UNARY:  'a * 'a -> (svalue,'a) token
val ID: (string) *  'a * 'a -> (svalue,'a) token
val LIT: (string) *  'a * 'a -> (svalue,'a) token
val BOOL: (bool) *  'a * 'a -> (svalue,'a) token
val NUM: (int) *  'a * 'a -> (svalue,'a) token
val INCLUDE:  'a * 'a -> (svalue,'a) token
val CHANNEL:  'a * 'a -> (svalue,'a) token
val BIND:  'a * 'a -> (svalue,'a) token
val UNLOG:  'a * 'a -> (svalue,'a) token
val LOG:  'a * 'a -> (svalue,'a) token
val NORM:  'a * 'a -> (svalue,'a) token
val REJECT:  'a * 'a -> (svalue,'a) token
val CHECK:  'a * 'a -> (svalue,'a) token
val TYPE:  'a * 'a -> (svalue,'a) token
val PROP:  'a * 'a -> (svalue,'a) token
val CONSTANT:  'a * 'a -> (svalue,'a) token
val REFUTE:  'a * 'a -> (svalue,'a) token
val PROVE:  'a * 'a -> (svalue,'a) token
val LEMMA:  'a * 'a -> (svalue,'a) token
val THEOREM:  'a * 'a -> (svalue,'a) token
val AXIOM:  'a * 'a -> (svalue,'a) token
val RIGHT:  'a * 'a -> (svalue,'a) token
val LEFT:  'a * 'a -> (svalue,'a) token
val ABORT:  'a * 'a -> (svalue,'a) token
val DARROW:  'a * 'a -> (svalue,'a) token
val BAR:  'a * 'a -> (svalue,'a) token
val OF:  'a * 'a -> (svalue,'a) token
val CASE:  'a * 'a -> (svalue,'a) token
val INR:  'a * 'a -> (svalue,'a) token
val INL:  'a * 'a -> (svalue,'a) token
val LAM:  'a * 'a -> (svalue,'a) token
val END:  'a * 'a -> (svalue,'a) token
val IN:  'a * 'a -> (svalue,'a) token
val EQUALS:  'a * 'a -> (svalue,'a) token
val ULET:  'a * 'a -> (svalue,'a) token
val LET:  'a * 'a -> (svalue,'a) token
val SND:  'a * 'a -> (svalue,'a) token
val FST:  'a * 'a -> (svalue,'a) token
val BANG:  'a * 'a -> (svalue,'a) token
val TOP:  'a * 'a -> (svalue,'a) token
val EQUIV:  'a * 'a -> (svalue,'a) token
val REVARROW:  'a * 'a -> (svalue,'a) token
val ARROW:  'a * 'a -> (svalue,'a) token
val CHOICE:  'a * 'a -> (svalue,'a) token
val LEQUIV:  'a * 'a -> (svalue,'a) token
val REVLOLLI:  'a * 'a -> (svalue,'a) token
val LOLLI:  'a * 'a -> (svalue,'a) token
val WITH:  'a * 'a -> (svalue,'a) token
val STAR:  'a * 'a -> (svalue,'a) token
val CARET:  'a * 'a -> (svalue,'a) token
val SEMI:  'a * 'a -> (svalue,'a) token
val TICK:  'a * 'a -> (svalue,'a) token
val COLON:  'a * 'a -> (svalue,'a) token
val DOT:  'a * 'a -> (svalue,'a) token
val COMMA:  'a * 'a -> (svalue,'a) token
val RBRACE:  'a * 'a -> (svalue,'a) token
val LBRACE:  'a * 'a -> (svalue,'a) token
val RBRACK:  'a * 'a -> (svalue,'a) token
val LBRACK:  'a * 'a -> (svalue,'a) token
val RPAREN:  'a * 'a -> (svalue,'a) token
val LPAREN:  'a * 'a -> (svalue,'a) token
val EOF:  'a * 'a -> (svalue,'a) token
end
signature Prop_LRVALS=
sig
structure Tokens : Prop_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
