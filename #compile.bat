@echo off
set COQ_PATH=coqc
REM set COQ_PATH=C:\Coq\bin\coqc

set PREFIX=-R . IPC2
@echo on

%COQ_PATH% %PREFIX% UserTactics
%COQ_PATH% %PREFIX% ListFacts
%COQ_PATH% %PREFIX% MiscFacts
%COQ_PATH% %PREFIX% Formula
%COQ_PATH% %PREFIX% FormulaFacts
%COQ_PATH% %PREFIX% Derivations
%COQ_PATH% %PREFIX% Diophantine
%COQ_PATH% %PREFIX% Encoding
%COQ_PATH% %PREFIX% Soundness
%COQ_PATH% %PREFIX% Completeness
%COQ_PATH% %PREFIX% MainResult
PAUSE