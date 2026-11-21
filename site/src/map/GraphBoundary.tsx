// A graph that throws while drawing shows a short notice in its own place, so the paper beside it,
// the reading position and the pane's controls stay. PageGuard (app/PageGuard.tsx) does the same for
// a whole page; this one sits around a pane or a drawing inside a page. The error goes to the console
// with the scope that failed; the reader sees no stack.
import { Component, type ReactNode } from "react";

interface Props {
  /** What is being drawn, for the console and as the reset key: a new scope tries again. */
  scope: string;
  children: ReactNode;
}

export class GraphBoundary extends Component<Props, { failed: boolean }> {
  state = { failed: false };

  static getDerivedStateFromError() {
    return { failed: true };
  }

  componentDidCatch(error: unknown) {
    console.error(`The graph (${this.props.scope}) failed to draw:`, error);
  }

  componentDidUpdate(previous: Props) {
    if (previous.scope !== this.props.scope && this.state.failed) this.setState({ failed: false });
  }

  render() {
    if (this.state.failed)
      return (
        <div className="graph-boundary" role="alert">
          <p>The diagram could not be drawn.</p>
          <p>Your paper position and selected statement are preserved.</p>
          <button type="button" onClick={() => this.setState({ failed: false })}>
            Try again
          </button>
        </div>
      );
    return this.props.children;
  }
}
