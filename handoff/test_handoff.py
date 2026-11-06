"""Small adversarial checks; no baseline download, compression, or proof run."""
from copy import deepcopy
import gzip
import json
from pathlib import Path
import stat
import tempfile
import zipfile

from build_handoff import validate_git_plan
from prepare_handoff import scan
from verify_handoff import safe_name, verify


def reject(label,function,message):
    try:
        function()
    except ValueError as error:
        if message not in str(error):
            raise AssertionError((label,'wrong rejection',str(error))) from error
        return label
    raise AssertionError('Accepted malformed fixture: '+label)


def main():
    tests=[]
    for name in ('../x','/x','C:x','a\\b','a/../b','a//b','CON.txt','x.','dir /x','AUX'):
        tests.append(reject(name,lambda name=name:safe_name(name),'archive name'))
    good=dict(snapshot_commit='a'*40,files=[dict(kind='git',path='a',archive_path='current/a',git_blob='1'),
                                           dict(kind='git',path='b',archive_path='current/b',git_blob='2')])
    assert validate_git_plan(good,{'a':'1','b':'2'})=={'a':'1','b':'2'}
    bad=deepcopy(good); bad['files'][0]['archive_path']='current/b'; bad['files'][1]['archive_path']='current/a'
    tests.append(reject('swapped destinations',lambda:validate_git_plan(bad,{'a':'1','b':'2'}),'destination'))
    missing=deepcopy(good); missing['files'].pop()
    tests.append(reject('omitted Git file',lambda:validate_git_plan(missing,{'a':'1','b':'2'}),'complete exact'))
    secret=json.dumps({''.join(('pass','word')):'mock-value-for-negative-test'}).encode()
    tests.append(reject('raw credential field',lambda:scan('fixture.json',secret),'Credential field'))
    tests.append(reject('gzip credential field',lambda:scan('fixture.json.gz',gzip.compress(secret)),'Credential field'))
    scan('fixture.json.gz',gzip.compress(b'{"status":"PASS"}'))
    with tempfile.TemporaryDirectory(prefix='handoff-negative-') as temporary:
        root=Path(temporary)
        for name,entries,message in [('case',[('x',None),('X',None)],'case-colliding'),
                                     ('link',[('link',stat.S_IFLNK|0o777)],'Nonregular')]:
            path=root/(name+'.zip')
            with zipfile.ZipFile(path,'w') as archive:
                for member,mode in entries:
                    info=zipfile.ZipInfo(member)
                    if mode is not None:
                        info.external_attr=mode<<16
                    archive.writestr(info,b'target')
            tests.append(reject(name,lambda path=path:verify(path),message))
    print(json.dumps(dict(status='PASS',small_negative_cases=len(tests),cases=tests),indent=2))


if __name__=='__main__':
    main()
