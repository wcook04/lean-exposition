// Who made this site and where the rest of his work is: names, titles and addresses as
// his own pages give them (Plectis, Plectis Atlas and the YouTube videos, 26 October 2026).

export const AUTHOR = "Will Cook";

export const LINKS = {
  /** His main website: the maths map, his Erdős problem research, his software and his videos. */
  plectis: "https://wcook04.github.io/plectis/",
  mathsMap: "https://wcook04.github.io/plectis/maths/universe.html",
  /** OpenAI's mathematics release beside the outside reports that assess it. */
  atlas: "https://wcook04.github.io/plectis-atlas/",
  atlasFamily: "https://wcook04.github.io/plectis-atlas/families/281.html",
  youtube: "https://www.youtube.com/@willcook2004",
  github: "https://github.com/wcook04",
  contact: "https://wcook04.github.io/plectis/docs/contact.html#get-in-touch",
  x: "https://x.com/cookie1234593",
} as const;

export interface Video {
  url: string;
  title: string;
  /** Running time in minutes, rounded. */
  minutes: number;
}

export const VIDEOS = {
  introduction: { url: "https://www.youtube.com/watch?v=U1z2-XaLe_w", title: "INTRODUCTION: Using AI for maths research and software", minutes: 6 },
  erdos257: { url: "https://www.youtube.com/watch?v=vXgIBy5C5X0", title: "Erdős #257: why some infinite sums cannot be fractions", minutes: 30 },
  mathsMap: { url: "https://www.youtube.com/watch?v=J2sX6nj3jOk", title: "Maths Map: how proofs, papers and explanations connect", minutes: 6 },
  atlas: { url: "https://www.youtube.com/watch?v=ugUObM3qpmM", title: "Plectis Atlas: compare maths papers with the reports that check them", minutes: 5 },
} satisfies Record<string, Video>;
