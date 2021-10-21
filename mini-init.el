(package-initialize)
(require 'agda2-mode)

;; Enter agda2-mode automatically when opening a .agda file
(add-to-list 'auto-mode-alist
    '("\\.agda\\'" . (lambda () (agda2-mode))))

;; Hide the tool bar and the menu bar
(menu-bar-mode 0)
(tool-bar-mode 0)
