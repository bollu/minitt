(define-derived-mode stlc-mode prog-mode
  "stlc"
  "Major mode for STLC as implemented by bollu.")
(add-to-list 'auto-mode-alist '("\\.stlc\\'" . stlc-mode))

(add-to-list 'lsp-language-id-configuration '(stlc-mode . "stlc"))
(lsp-register-client
 (make-lsp-client :new-connection (lsp-stdio-connection "stlc")
                  :activation-fn (lsp-activate-on "stlc")
		  :major-modes '(stlc-mode)
                  :server-id 'stlc))

