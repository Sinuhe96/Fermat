import json, urllib.request

REPOS = [
    "bartowski/Qwen2.5-Math-7B-Instruct-GGUF",
    "AI-MO/Kimina-Prover-Preview-Distill-7B",
    "Goedel-LM/Goedel-Prover-SFT",
    "Qwen/Qwen2.5-Math-7B-Instruct",
]

for repo in REPOS:
    print("=" * 70)
    print(repo)
    try:
        url = "https://huggingface.co/api/models/" + repo
        data = json.load(urllib.request.urlopen(url, timeout=25))
        sibs = data.get("siblings", [])
        ggufs = [s.get("rfilename", "") for s in sibs
                 if str(s.get("rfilename", "")).endswith(".gguf")]
        print("  total files:", len(sibs), "| gguf files:", len(ggufs))
        for f in sorted(ggufs)[:20]:
            print("   -", f)
    except Exception as e:
        print("  FAIL", repr(e)[:160])
