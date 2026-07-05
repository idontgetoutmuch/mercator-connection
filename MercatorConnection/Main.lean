import VersoBlog
import MercatorConnection

open Verso Genre Blog Site Syntax

def blog : Site := site MercatorConnection.FrontPage /
  "about"MercatorConnection.About
  "blog" MercatorConnection.Posts with
    MercatorConnection.Posts.FirstPost
    MercatorConnection.Posts.VersionStableLemmas

def main := blogMain .default blog
