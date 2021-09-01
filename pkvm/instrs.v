From isla Require Import isla_lang.
Require Import isla.pkvm.a7400.
Require Import isla.pkvm.a7404.
Require Import isla.pkvm.a7408.
Require Import isla.pkvm.a740c.
Require Import isla.pkvm.a7410.
Require Import isla.pkvm.a7414.
Require Import isla.pkvm.a7418.
Require Import isla.pkvm.a741c.
Require Import isla.pkvm.a7420.
Require Import isla.pkvm.a7424.
Require Import isla.pkvm.a7428.
Require Import isla.pkvm.a742c.
Require Import isla.pkvm.a7430.
Require Import isla.pkvm.a7434.
Require Import isla.pkvm.a7438.
Require Import isla.pkvm.a743c.


Definition instr_map := [
(0x7400%Z, a7400)
; (0x7404%Z, a7404)
; (0x7408%Z, a7408)
; (0x740c%Z, a740c)
; (0x7410%Z, a7410)
; (0x7414%Z, a7414)
; (0x7418%Z, a7418)
; (0x741c%Z, a741c)
; (0x7420%Z, a7420)
; (0x7424%Z, a7424)
; (0x7428%Z, a7428)
; (0x742c%Z, a742c)
; (0x7430%Z, a7430)
; (0x7434%Z, a7434)
; (0x7438%Z, a7438)
; (0x743c%Z, a743c)
].