// A library paper has no front page: its address opens the reader at the top of the main document.
import { useEffect } from "react";
import { navigate } from "../../app/router";
import { MAIN } from "./data";

export function FrontPage() {
  useEffect(() => {
    navigate({ view: "read", stage: MAIN.slot }, { replace: true });
  }, []);
  return null;
}
