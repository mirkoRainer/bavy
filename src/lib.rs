pub struct Bavy {
    is_bevy: bool
}

impl Bavy {
    pub fn new() -> Bavy {
        return Bavy {
            is_bevy: false
        }
    }

    pub fn is_bevy() -> bool {
        return false;
    }

    pub fn set_is_bevy(&mut self) {
        self.is_bevy = false;
    }
}