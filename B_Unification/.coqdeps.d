terms.vo terms.glob terms.v.beautified: terms.v
terms.vio: terms.v
poly.vo poly.glob poly.v.beautified: poly.v terms.vo
poly.vio: poly.v terms.vio
terms_unif.vo terms_unif.glob terms_unif.v.beautified: terms_unif.v terms.vo
terms_unif.vio: terms_unif.v terms.vio
poly_unif.vo poly_unif.glob poly_unif.v.beautified: poly_unif.v poly.vo
poly_unif.vio: poly_unif.v poly.vio
lowenheim.vo lowenheim.glob lowenheim.v.beautified: lowenheim.v terms_unif.vo
lowenheim.vio: lowenheim.v terms_unif.vio
sve.vo sve.glob sve.v.beautified: sve.v poly_unif.vo
sve.vio: sve.v poly_unif.vio
