// A modal surface on the native <dialog>: the browser makes the rest of the
// page inert and keeps focus inside; Escape closes it; closing returns focus
// to whatever opened it. Used for the phone's Sections and Passage details,
// the "Same topic in…" chooser and an expanded formula.

import { useEffect, useId, useLayoutEffect, useRef } from "react";

interface Props {
  title: string;
  /** Visually hide the title when the content names itself. */
  hideTitle?: boolean;
  /** "sheet" rises from the bottom on phones; "side" stands at an edge on wider screens; "centre" is a dialog. */
  placement: "sheet" | "side-start" | "side-end" | "centre";
  className?: string;
  onClose(): void;
  children: React.ReactNode;
}

export function Modal({ title, hideTitle, placement, className, onClose, children }: Props) {
  const ref = useRef<HTMLDialogElement>(null);
  const titleId = useId();
  const opener = useRef<Element | null>(null);
  const closeRef = useRef(onClose);
  closeRef.current = onClose;

  useLayoutEffect(() => {
    const dialog = ref.current;
    if (!dialog) return;
    opener.current = document.activeElement;
    if (!dialog.open) dialog.showModal();
    // Start on the first control after the title bar, or the title itself.
    const first = dialog.querySelector<HTMLElement>("[data-autofocus]") ?? dialog.querySelector<HTMLElement>(".modal__title");
    first?.focus({ preventScroll: true });
    return () => {
      if (dialog.open) dialog.close();
      const back = opener.current as HTMLElement | null;
      if (back?.isConnected) back.focus({ preventScroll: true });
    };
  }, []);

  useEffect(() => {
    const dialog = ref.current;
    if (!dialog) return;
    const onCancel = (event: Event) => {
      event.preventDefault();
      closeRef.current();
    };
    dialog.addEventListener("cancel", onCancel);
    return () => dialog.removeEventListener("cancel", onCancel);
  }, []);

  return (
    <dialog
      ref={ref}
      className={`modal modal--${placement}${className ? ` ${className}` : ""}`}
      aria-labelledby={titleId}
      data-modal-open=""
      onClick={(event) => {
        // A click on the backdrop (the dialog box itself, outside its content) closes it.
        if (event.target === ref.current) closeRef.current();
      }}
    >
      <div className="modal__box">
        <header className="modal__bar">
          <h2 id={titleId} className={`modal__title${hideTitle ? " visually-hidden" : ""}`} tabIndex={-1}>
            {title}
          </h2>
          <button type="button" className="modal__close" aria-label={`Close ${title}`} onClick={() => closeRef.current()}>
            <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
              <path d="M2.5 2.5l7 7M9.5 2.5l-7 7" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
            </svg>
          </button>
        </header>
        <div className="modal__body">{children}</div>
      </div>
    </dialog>
  );
}
