from distutils.core import setup
import py2exe, sys, os

sys.argv.append('py2exe')

setup(
    options = {'py2exe': {'bundle_files': 2, 'compressed': True}},
    windows = [{'script': 'amkeditor.pyw', 'icon_resources': [(1, 'amkeditor.ico')]}],
    zipfile = None
)
