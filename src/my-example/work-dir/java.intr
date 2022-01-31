(((!=
   ((arg_types ((Int Top) (Int Top))) (output_types ((Int Top) (Int Top)))
    (result_type
     (Int (NamedPred rel-!=-out (((Var $0) () None) ((Var $1) () None)))))))
  (%
   ((arg_types ((Int Top) (Int Top))) (output_types ((Int Top) (Int Top)))
    (result_type
     (Int (NamedPred mod-%-out (((Var $0) () None) ((Var $1) () None)))))))
  (&&
   ((arg_types ((Int Top) (Int Top))) (output_types ((Int Top) (Int Top)))
    (result_type
     (Int (NamedPred plus-+-out (((Var $0) () None) ((Var $1) () None)))))))
  (*
   ((arg_types ((Int Top) (Int Top))) (output_types ((Int Top) (Int Top)))
    (result_type
     (Int (NamedPred times-*-out (((Var $0) () None) ((Var $1) () None)))))))
  (+
   ((arg_types ((Int Top) (Int Top))) (output_types ((Int Top) (Int Top)))
    (result_type
     (Int (NamedPred plus-+-out (((Var $0) () None) ((Var $1) () None)))))))
  (-
   ((arg_types ((Int Top) (Int Top))) (output_types ((Int Top) (Int Top)))
    (result_type
     (Int (NamedPred minus---out (((Var $0) () None) ((Var $1) () None)))))))
  (<
   ((arg_types ((Int Top) (Int Top))) (output_types ((Int Top) (Int Top)))
    (result_type
     (Int (NamedPred rel-<-out (((Var $0) () None) ((Var $1) () None)))))))
  (<=
   ((arg_types ((Int Top) (Int Top))) (output_types ((Int Top) (Int Top)))
    (result_type
     (Int (NamedPred rel-<=-out (((Var $0) () None) ((Var $1) () None)))))))
  (=
   ((arg_types ((Int Top) (Int Top))) (output_types ((Int Top) (Int Top)))
    (result_type
     (Int (NamedPred rel-=-out (((Var $0) () None) ((Var $1) () None)))))))
  (>
   ((arg_types ((Int Top) (Int Top))) (output_types ((Int Top) (Int Top)))
    (result_type
     (Int (NamedPred rel->-out (((Var $0) () None) ((Var $1) () None)))))))
  (>=
   ((arg_types ((Int Top) (Int Top))) (output_types ((Int Top) (Int Top)))
    (result_type
     (Int (NamedPred rel->=-out (((Var $0) () None) ((Var $1) () None)))))))
  (regnant$flag_1
   ((arg_types ((Int Top))) (output_types ((Int Top)))
    (result_type (Int (NamedPred regnant$flag_1 (((Var $0) () None)))))))
  (||
   ((arg_types ((Int Top) (Int Top))) (output_types ((Int Top) (Int Top)))
    (result_type
     (Int (NamedPred times-*-out (((Var $0) () None) ((Var $1) () None))))))))
 ((!= uneq) (< <) (<= <=) (= =) (> >) (>= >=)) generated.smt)
