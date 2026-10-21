from pathlib import Path
p=Path('work/thirdreal20261021_rational_repair.py')
s=p.read_text().replace("raw=json.loads(Path('work/thirdreal20261021_rational_scan_100.json').read_text());missing=raw['missing'];cert=[];start=time.time()", "maxn=int(sys.argv[1]) if len(sys.argv)>1 else 100\n from thirdreal20261021_rational_logbounds import exact_fast\n exact=exact_fast\n raw=json.loads(Path(f'work/thirdreal20261021_rational_scan_{maxn}.json').read_text());missing=raw['missing'];cert=[];start=time.time()")
s=s.replace("Path('work/thirdreal20261021_rational_repaired_100.json')", "Path(f'work/thirdreal20261021_rational_repaired_{maxn}.json')")
p.write_text(s)
