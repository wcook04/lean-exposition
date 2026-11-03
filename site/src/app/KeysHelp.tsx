// The `?` key: the same list of keys the About page gives, in the browser's own modal dialog,
// so focus, Escape and the backdrop behave as they do anywhere.

import { useEffect, useRef } from "react";
import { routeHref } from "./router";
import { SITE_KEYS } from "./keys";

export function KeyList() {
  return (
    <dl className="keylist">
      {SITE_KEYS.map(({ keys, does }) => (
        <div key={does}>
          <dt>
            {keys.map((key) => (
              <kbd key={key} className="kbd">
                {key}
              </kbd>
            ))}
          </dt>
          <dd>{does}</dd>
        </div>
      ))}
    </dl>
  );
}

export function KeysHelp({ onClose }: { onClose(): void }) {
  const ref = useRef<HTMLDialogElement>(null);
  useEffect(() => {
    const dialog = ref.current;
    if (dialog && !dialog.open) dialog.showModal();
  }, []);
  return (
    <dialog
      ref={ref}
      className="keys-help"
      aria-labelledby="keys-help-title"
      onClose={onClose}
      onClick={(event) => {
        if (event.target === ref.current) ref.current?.close();
      }}
    >
      <div className="keys-help__body">
        <h2 id="keys-help-title">Keys</h2>
        <KeyList />
        <p className="keys-help__foot">
          <a href={routeHref({ view: "about", anchor: "using" })} onClick={() => ref.current?.close()}>
            How to use this site
          </a>
          <button type="button" className="control" onClick={() => ref.current?.close()}>
            Close
          </button>
        </p>
      </div>
    </dialog>
  );
}
