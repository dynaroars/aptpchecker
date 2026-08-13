-- AptpCheck: a formally-verified checker for APTP neural-network proofs.
-- See DESIGN.md for the architecture and soundness decomposition.
import AptpCheck.Numeric.Float
import AptpCheck.Cert.LinComb
import AptpCheck.Cert.LinCon
import AptpCheck.Coverage.Tautology
import AptpCheck.Pipeline.Compose
import AptpCheck.Pipeline.Affine
import AptpCheck.Ast.Sexpr
import AptpCheck.Ast.Aptp
import AptpCheck.Ast.Net
import AptpCheck.Model.Network
import AptpCheck.Model.Encoding
import AptpCheck.Model.Encoder
import AptpCheck.Model.EncodingSound
import AptpCheck.Cert.Vipr
import AptpCheck.Ast.Vipr
import AptpCheck.Ast.NetRoundtrip
import AptpCheck.Ast.AptpRoundtrip
