import VersoManual
import LeanVIPRManual

open Verso.Genre.Manual

def config : Config where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2

def main := manualMain (%doc LeanVIPRManual) (config := { config with })
