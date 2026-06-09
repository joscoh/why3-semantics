(*Contains the definition of [pi_dom_full], formerly part of the
  definition of [pi_dom] in Interp.v but now describing a particular
  interpretation that happens to set all ADT interps to W-types.
  We show in ADTFullProps.v that [pi_dom_full] satisfies
  the ADT spec in [pi_funpred] and in ADTInterp.v give the explicit
  construction of such an interp.*)
Require Export Interp IndTypes.


Record pi_dom_full (gamma: context) (pd: pi_dom) := {
  

  (*ADTs: they are the corresponding W type created by [mk_adts],
    with the typesym and typevar map coming from sorts on which
    the type is applied*)

    adts: forall (m: mut_adt) (srts: list sort)
    (a: alg_datatype) (m_in: mut_in_ctx m gamma) (Hin: adt_in_mut a m)
    (Hlen: length srts = length (m_params m)),
    (domain (dom_aux pd)) (s_cons (adt_name a) srts) =
    IndTypes.adt_rep m srts (dom_aux pd) a Hin;

}.
