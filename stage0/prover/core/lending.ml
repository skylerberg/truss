let holds_where_lent (clause : Mir.formula) =
  Contracts.mentions_result clause && not (Contracts.mentions_final_result clause)

let lend_part (frame : State.frame) origin (mode : Language.Mode.t) ~handed ~lends_places
    ~write_back =
  let location = Facts.locate frame origin in
  match frame.lent_part_type with
  | None -> Facts.raise_unsupported location Lent_part_outside_lending_method
  | Some part_type ->
      let lent = { frame with result = Some handed } in
      Validity.check_valid lent location part_type handed ~deep:true ~moment:Part_lent;
      ( { State.lent_frame = lent; lent_origin = origin },
        if mode = Language.Mode.Mut && lends_places then begin
          let final = Encoding.arrive lent "lent" part_type in
          Validity.assume_valid lent part_type final;
          let written : State.frame = write_back lent final in
          { written with final_result = Some final }
        end
        else { lent with final_result = Some handed } )

let bind_final (frame : State.frame) final = { frame with final_result = Some final }

let read_final_result (frame : State.frame) =
  match frame.final_result with
  | Some final -> final
  | None ->
      Facts.raise_bug "`%s` reads `final(result)` where no lend has ended"
        (Resolve.Names.show_key frame.source.key)
