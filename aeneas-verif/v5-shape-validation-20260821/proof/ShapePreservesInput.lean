import ShapeSource.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5ShapeValidationProof

open V5ShapeValidationSource

attribute [local simp]
  core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  core.convert.FromSame core.convert.FromSame.from

private def validatedShape
    (traceLogSize domainLogSize : Std.U8)
    (queryCount : Std.U16)
    (openingPoints : Std.U8)
    (c1Columns c2Columns : Std.U16)
    (c1Layer0Tag c2Layer0Tag : Std.U8)
    (laterLayerTags : Array Std.U8 3#usize) :
    circle_pcs_shape.CirclePcsShape :=
  {
    trace_log_size := traceLogSize
    domain_log_size := domainLogSize
    query_count := queryCount
    opening_points := openingPoints
    c1_columns := c1Columns
    c2_columns := c2Columns
    c1_layer0_tag := c1Layer0Tag
    c2_layer0_tag := c2Layer0Tag
    later_layer_tags := laterLayerTags
  }

private def validationPost
    (expected : circle_pcs_shape.CirclePcsShape) :
    core.result.Result circle_pcs_shape.CirclePcsShape
      circle_pcs_shape.CirclePcsShapeError → Prop
  | .Ok output => output = expected
  | .Err _ => True

private theorem fromResidualNeverReturnsSuccessfulShape
    (residual : core.result.Result core.convert.Infallible
      circle_pcs_shape.CirclePcsShapeError)
    (output : circle_pcs_shape.CirclePcsShape)
    (h : core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      circle_pcs_shape.CirclePcsShape
      (core.convert.FromSame circle_pcs_shape.CirclePcsShapeError) residual =
      .ok (.Ok output)) : False := by
  cases residual with
  | Ok impossible => exact nomatch impossible
  | Err error => simp at h

private theorem validateLoopBody_done
    (traceLogSize domainLogSize : Std.U8)
    (queryCount : Std.U16)
    (openingPoints : Std.U8)
    (c1Columns c2Columns : Std.U16)
    (c1Layer0Tag c2Layer0Tag : Std.U8)
    (laterLayerTags : Array Std.U8 3#usize)
    (tags : Array Std.U8 5#usize)
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.iter.adapters.copied.Copied (core.slice.iter.Iter Std.U8)))
    (output : core.result.Result circle_pcs_shape.CirclePcsShape
      circle_pcs_shape.CirclePcsShapeError)
    (h : circle_pcs_shape.CirclePcsShape.validate_loop.body
      traceLogSize domainLogSize queryCount openingPoints c1Columns c2Columns
      c1Layer0Tag c2Layer0Tag laterLayerTags tags iter = .ok (.done output)) :
    validationPost
      (validatedShape traceLogSize domainLogSize queryCount openingPoints
        c1Columns c2Columns c1Layer0Tag c2Layer0Tag laterLayerTags)
  output := by
  unfold circle_pcs_shape.CirclePcsShape.validate_loop.body at h
  simp only [Bind.bind, Aeneas.Std.bind] at h
  repeat' split at h
  all_goals cases output <;> simp_all [validationPost, validatedShape]

private theorem validateLoop_success
    (traceLogSize domainLogSize : Std.U8)
    (queryCount : Std.U16)
    (openingPoints : Std.U8)
    (c1Columns c2Columns : Std.U16)
    (c1Layer0Tag c2Layer0Tag : Std.U8)
    (laterLayerTags : Array Std.U8 3#usize)
    (tags : Array Std.U8 5#usize)
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.iter.adapters.copied.Copied (core.slice.iter.Iter Std.U8)))
    (output : core.result.Result circle_pcs_shape.CirclePcsShape
      circle_pcs_shape.CirclePcsShapeError)
    (h : circle_pcs_shape.CirclePcsShape.validate_loop iter
      traceLogSize domainLogSize queryCount openingPoints c1Columns c2Columns
      c1Layer0Tag c2Layer0Tag laterLayerTags tags = .ok output) :
    validationPost
      (validatedShape traceLogSize domainLogSize queryCount openingPoints
        c1Columns c2Columns c1Layer0Tag c2Layer0Tag laterLayerTags)
      output := by
  unfold circle_pcs_shape.CirclePcsShape.validate_loop at h
  revert iter output
  apply Aeneas.Std.loop.fixpoint_induct
    (motive := fun loop => ∀ iter output,
      loop iter = .ok output →
        validationPost
          (validatedShape traceLogSize domainLogSize queryCount openingPoints
            c1Columns c2Columns c1Layer0Tag c2Layer0Tag laterLayerTags)
          output)
  · apply Lean.Order.admissible_pi
    intro iter
    apply Lean.Order.admissible_pi
    intro output
    apply Lean.Order.admissible_apply
      (β := fun _ : core.iter.adapters.enumerate.Enumerate
        (core.iter.adapters.copied.Copied (core.slice.iter.Iter Std.U8)) =>
          Aeneas.Std.Result
            (core.result.Result circle_pcs_shape.CirclePcsShape
              circle_pcs_shape.CirclePcsShapeError))
      (P := fun _ result => result = Aeneas.Std.Result.ok output →
        validationPost
          (validatedShape traceLogSize domainLogSize queryCount openingPoints
            c1Columns c2Columns c1Layer0Tag c2Layer0Tag laterLayerTags)
          output)
      iter
    apply Lean.Order.admissible_flatOrder
    simp
  · intro loop ih iter output h
    generalize hbody :
      circle_pcs_shape.CirclePcsShape.validate_loop.body
        traceLogSize domainLogSize queryCount openingPoints c1Columns c2Columns
        c1Layer0Tag c2Layer0Tag laterLayerTags tags iter = bodyResult at h
    cases bodyResult with
    | fail error => simp [hbody] at h
    | div => simp [hbody] at h
    | ok flow =>
      cases flow with
      | cont nextIter =>
        simp [hbody] at h
        exact ih nextIter output h
      | done result =>
        simp [hbody] at h
        subst output
        exact validateLoopBody_done traceLogSize domainLogSize queryCount
          openingPoints c1Columns c2Columns c1Layer0Tag c2Layer0Tag
          laterLayerTags tags iter result hbody

/-- The transparent Aeneas translation of the production validator can only
return the input shape on its successful branch. -/
theorem generatedValidationSuccessPreservesInput
    (input output : circle_pcs_shape.CirclePcsShape)
    (h : circle_pcs_shape.formal_validate_shape input =
      .ok (.Ok output)) :
    output = input := by
  unfold circle_pcs_shape.formal_validate_shape at h
  unfold circle_pcs_shape.CirclePcsShape.validate at h
  simp only [Bind.bind, Aeneas.Std.bind] at h
  repeat' split at h
  all_goals try simp_all
  all_goals try {
    exact (fromResidualNeverReturnsSuccessfulShape _ _ h).elim
  }
  have hp := validateLoop_success
    input.trace_log_size input.domain_log_size input.query_count
    input.opening_points input.c1_columns input.c2_columns
    input.c1_layer0_tag input.c2_layer0_tag input.later_layer_tags
    _ _ (.Ok output) h
  change output = validatedShape
    input.trace_log_size input.domain_log_size input.query_count
    input.opening_points input.c1_columns input.c2_columns
    input.c1_layer0_tag input.c2_layer0_tag input.later_layer_tags at hp
  calc
    output = validatedShape
      input.trace_log_size input.domain_log_size input.query_count
      input.opening_points input.c1_columns input.c2_columns
      input.c1_layer0_tag input.c2_layer0_tag input.later_layer_tags := hp
    _ = input := by cases input; rfl

end V5ShapeValidationProof
