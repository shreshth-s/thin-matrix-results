#!/usr/bin/env python3
"""Independent no-fallback wrapper for full light-gauge backend integration."""
from pathlib import Path
import importlib.util

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

joint=load('joint_cap_encoder',Path(__file__).resolve().parent.parent/'joint-box-cap-improvement/check_joint_cap_boxes.py')
gauge=load('light_gauge_backend',
           Path(__file__).with_name('check_light_source_gauges.py'))
original=gauge.cache.encode
boxes_by_id={}
reads=dict(box=0,residual=0)


def encode(array,L,m,t,side,stats):
    canonical=original(array,L,m,t,side,stats)
    boxes=joint.joint_cap_encoder(array,L,m,t,side)
    assert all(canonical[word][0]==value for word,value in boxes.items())
    boxes_by_id[id(canonical)]=(boxes,2*m)
    return canonical


class StrictView:
    def __init__(self,selected,canonical):
        self.selected=selected
        self.boxes,self.inner_count=boxes_by_id[id(canonical)]

    def __contains__(self,word):
        return word in self.selected or word in self.boxes

    def __getitem__(self,word):
        if sum(label>=4 for label in word)==self.inner_count:
            assert word in self.selected,('missing structured residual',word)
            reads['residual']+=1
            return self.selected[word]
        assert 5 not in word
        assert word in self.boxes,('missing smaller box-encoder leaf',word)
        reads['box']+=1
        return (self.boxes[word],)


if __name__=='__main__':
    gauge.cache.encode=encode
    gauge.shifted.View=StrictView
    gauge.main()
    assert joint.stats['encoders']==208
    assert joint.stats['omitted_leaves']>0 and min(reads.values())>0
    print('PASS independent joint-cap box-only encoders:',joint.stats)
    print('PASS strict no-fallback execution reads:',reads)
    print('Canonical caches above are comparison oracles only, never execution fallbacks.')
