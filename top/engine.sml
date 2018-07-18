(* non-focusing rules; unordered list database *)
structure Engine1_Basic = EngineFn (structure DB = DBTriv
                                    structure Gen = BasicRuleGen)

(* focusing rules; unordered list database *)
structure Engine1_Focusing = EngineFn (structure DB = DBTriv
                                       structure Gen = RuleGen)

(* non-focusing rules; indexed database *)
structure Engine2_Basic = EngineFn (structure DB = DBIndexed
                                    structure Gen = BasicRuleGen)

(* focusing rules; indexed database *)
structure Engine2_Focusing = EngineFn (structure DB = DBIndexed
                                       structure Gen = RuleGen)



(* Select a suitable engine. *)
structure Engine = Engine2_Focusing
