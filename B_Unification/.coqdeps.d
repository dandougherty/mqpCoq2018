terms.vo terms.glob terms.v.beautified: terms.v
terms.vio: terms.v
poly.vo poly.glob poly.v.beautified: poly.v terms.vo
poly.vio: poly.v terms.vio
poly_unif.vo poly_unif.glob poly_unif.v.beautified: poly_unif.v poly.vo
poly_unif.vio: poly_unif.v poly.vio
sve.vo sve.glob sve.v.beautified: sve.v poly_unif.vo
sve.vio: sve.v poly_unif.vio
lowenheim_formula.vo lowenheim_formula.glob lowenheim_formula.v.beautified: lowenheim_formula.v terms.vo
lowenheim_formula.vio: lowenheim_formula.v terms.vio
lowenheim_proof.vo lowenheim_proof.glob lowenheim_proof.v.beautified: lowenheim_proof.v lowenheim_formula.vo
lowenheim_proof.vio: lowenheim_proof.v lowenheim_formula.vio
